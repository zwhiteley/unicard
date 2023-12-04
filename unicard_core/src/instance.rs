use std::fmt::{Display, Formatter};
use wasmtime::{Error, Instance, Store, Trap};
use crate::module::{ApiVersion, GameId, GameManifest, GameModule, GameVersion};

/// An instance of a Unicard Game Module.
pub(crate) struct GameInstance<'a> {
    /// The manifest of the Unicard Game Module (from which the instance was instantiated).
    pub manifest: &'a GameManifest,

    /// The WebAssembly store.
    store: Store<()>,

    /// The WebAssembly instance.
    instance: Instance
}

impl<'a> GameInstance<'a> {
    /// The name of the api version function.
    const FN_API_VERSION: &'static str = "api_version";

    /// The name of the game id function.
    const FN_GAME_ID: &'static str = "game_id";

    /// The name of the game version function.
    const FN_GAME_VERSION: &'static str = "game_version";

    /// Instantiate a Unicard Game Module.
    pub fn new(game_module: &'a GameModule) -> Result<Self, RuntimeError> {
        // NOTE: we do not have to verify the targeted Unicard API version is supported, as this
        // is already an invariant of `GameModule`.

        // NOTE 2: we only verify the existence of functions when they are used -- there is
        //         no point verifying they exist, except perhaps for development purposes,
        //         as it is impossible they are implemented correctly anyway. This functionality
        //         should **NOT** be relied on for actual game module implementations (some
        //         runtime implementations may instead opt to check the functions here, some
        //         may call the functions under different circumstances, etc).

        let mut store = Store::new(game_module.module.engine(), ());
        let instance = match Instance::new(&mut store, &game_module.module, &[]) {
            Ok(instance) => instance,
            Err(error) => return RuntimeError::from_error(error)
        };

        // Check the API version first, as that is the only function that is guaranteed to
        // exist for all game modules
        let api_version = {
            let fn_api_version = match instance.get_typed_func(&mut store, Self::FN_API_VERSION) {
                Ok(fnc) => fnc,
                Err(error) => return Err(RuntimeError::InvalidApi(InvalidApiError(error)))
            };

            let result: i32 = match fn_api_version.call(&mut store, ()) {
                Ok(result) => result,
                Err(error) => return RuntimeError::from_error(error)
            };

            match ApiVersion::try_from(result as u32) {
                Ok(value) => value,
                Err(_) => return Err(RuntimeError::InvalidApi(InvalidApiError(Error::msg("api version returned is zero"))))
            }
        };

        if api_version != game_module.manifest().info.api_version {
            return Err(RuntimeError::InvalidApi(InvalidApiError(Error::msg("api version does not match that of manifest"))))
        }

        // Check game id and game version
        let game_id = {
            let fn_game_id = match instance.get_typed_func(&mut store, Self::FN_GAME_ID) {
                Ok(value) => value,
                Err(error) => return Err(RuntimeError::InvalidApi(InvalidApiError(error)))
            };

            // NOTE: at the time of writing, neither wasmtime nor Rust has first-class support
            // for v128s, so we use two i64s instead
            let game_id_parts: (i64, i64) = match fn_game_id.call(&mut store, ()) {
                Ok(value) => value,
                Err(error) => return RuntimeError::from_error(error)
            };

            let game_id_hi = u128::from(game_id_parts.0 as u64) << u64::BITS;
            let game_id_lo = u128::from(game_id_parts.1 as u64);
            let game_id_u128 = game_id_hi | game_id_lo;

            GameId::from(game_id_u128)
        };

        let game_version = {
            let fn_game_version = match instance.get_typed_func(&mut store, Self::FN_GAME_VERSION) {
                Ok(value) => value,
                Err(error) => return Err(RuntimeError::InvalidApi(InvalidApiError(error)))
            };

            let game_version_tuple: (i32, i32, i32) = match fn_game_version.call(&mut store, ()) {
                Ok(value) => value,
                Err(error) => return RuntimeError::from_error(error)
            };

            GameVersion {
                major: game_version_tuple.0 as u32,
                minor: game_version_tuple.1 as u32,
                patch: game_version_tuple.2 as u32,
            }
        };

        if game_id != game_module.manifest().info.id {
            return Err(RuntimeError::InvalidApi(InvalidApiError(Error::msg("game_id does not match manifest"))));
        }

        if game_version != game_module.manifest().info.game_version {
            return Err(RuntimeError::InvalidApi(InvalidApiError(Error::msg("game_version does not match manifest"))));
        }

        Ok(Self {
            manifest: game_module.manifest(),
            store, instance
        })
    }
}

/// An error which occurred during the execution of a Game Module.
#[derive(Debug)]
pub enum RuntimeError {
    /// A required API was either missing from the Game Module, has an incorrect
    /// signature (e.g., returns an `i32` where an `i64` is expected), or is
    /// implemented incorrectly.
    ///
    /// A possible reason for this error is an incorrect manifest (i.e., a user could
    /// try to mess with the manifest, causing it to be inconsistent with the binary,
    /// resulting in an error being blamed on a binary mis-implementation, rather than
    /// the illicit modification of the manifest).
    InvalidApi(InvalidApiError),

    /// A Wasm32 trap occurred.
    ///
    /// For example, reaching an `unreachable` instruction.
    WasmTrap(WasmTrapError),

    /// A host trap occurred.
    ///
    /// This is caused when a function provided by the runtime is used incorrectly.
    HostTrap(HostTrapError)
}

impl RuntimeError {
    /// Convert an anyhow error to a runtime error.
    ///
    /// Assumes non-traps are API mis-implementations.
    fn from_error<T>(error: Error) -> Result<T, Self> {
        let root_cause = error.root_cause();

        if root_cause.is::<Trap>() {
            Err(Self::WasmTrap(WasmTrapError(error)))
        } else if let Some(host_error) = root_cause.downcast_ref::<HostTrapError>() {
            Err(Self::HostTrap(host_error.clone()))
        } else {
            Err(Self::InvalidApi(InvalidApiError(error)))
        }
    }
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidApi(_) => f.write_str("the API exposed by the binary is invalid"),
            Self::WasmTrap(_) => f.write_str("a runtime trap occurred"),
            Self::HostTrap(_) => f.write_str("a host trap occurred")
        }
    }
}

impl std::error::Error for RuntimeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidApi(error) => Some(error),
            Self::WasmTrap(error) => Some(error),
            Self::HostTrap(error) => Some(error)
        }
    }
}

/// The API of the wasm32 binary is incorrect.
///
/// There are multiple causes for such an error:
///
/// * A required export is missing from the binary.
/// * The signature of a required export is different to that of the actual export.
/// * The required export is implemented incorrectly.
#[derive(Debug)]
pub struct InvalidApiError(Error);

impl Display for InvalidApiError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for InvalidApiError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(self.0.as_ref())
    }
}

/// A wasm32 trap occurred.
///
/// An example of this includes running into an `unreachable` instruction.
#[derive(Debug)]
pub struct WasmTrapError(Error);

impl Display for WasmTrapError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for WasmTrapError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(self.0.as_ref())
    }
}

/// A host-caused trap.
///
/// This occurs when an export, usually a function, exported by the runtime is misused.
#[derive(Debug, Clone)]
pub(crate) enum HostTrapError {}

impl Display for HostTrapError {
    fn fmt(&self, _: &mut Formatter<'_>) -> std::fmt::Result {
        unreachable!("it is impossible to create a `HostTrap` as it is an empty enum")
    }
}

impl std::error::Error for HostTrapError {}
