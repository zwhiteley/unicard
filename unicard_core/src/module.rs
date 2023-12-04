use serde::de::{Unexpected, Visitor};
use serde::ser::SerializeTuple;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt::{Display, Formatter, Write};
use std::io::{self, Read, Seek};
use std::num::{IntErrorKind, NonZeroU32};
use wasmtime::{Error, Module};
use zip::result::ZipError;
use zip::ZipArchive;

/// A Game Module.
///
/// A (Unicard) Game Module is a file which contains the instructions and assets pertaining to
/// a particular card game (e.g., Rummy), which can be executed by a Unicard runtime.
///
/// # Format
///
/// The Game Module file format is fairly simple -- it is a zip archive which contains two
/// files:
///
/// * The manifest file, `manifest.toml`, which describes the Game Module (e.g., the name of the
///   Game Module, its version, the Unicard API it utilises, etc). This file is a TOML-formatted
///   file which contains a [`GameManifest`] document.
///
/// * The binary file, `binary`, which contains the instructions of the underlying card game
///   in the form of a binary-encoded WASM module. (It should be noted that implementations --
///   including this one -- may also accept text-encoded WASM modules, although this is not
///   mandated.)
///
/// Additional files within the zip archive may cause issues.
///
/// # Remarks
///
/// Runtimes may impose size limits on the manifest and binary files.
///
/// The binary file may expose methods which provide information about the Game Module (e.g., an
/// `api_version` function which returns the Unicard API function the Game Module uses), despite
/// it being detailed in the manifest file.
///
/// Creating a `GameModule` is an expensive operation -- if only the manifest is required,
/// use [`GameManifest::from_module_file`] instead.
pub struct GameModule {
    /// The manifest of the Game Module.
    manifest: GameManifest,

    /// The compiled Game Module binary.
    ///
    /// # Remarks
    ///
    /// We include it directly as a [`Module`], and not a [`Vec<u8>`](Vec), as an optimisation:
    /// compiling a module is very expensive, so doing it once and storing the compiled result
    /// is much more efficient than storing the bytes and making a separate compilation for
    /// each instantiation.
    pub(crate) module: Module,
}

/// The manifest of a Game Module.
///
/// This structure contains (most of) the metadata related to the Game Module (e.g., its name).
///
/// # TOML Format
///
/// A manifest TOML document contains the following fields:
///
/// * An `info` field which contains a [`GameInfo`] table.
///
/// # Example
///
/// ```toml
/// [info]
/// id = "1178D217398AB"
/// name = "example-game"
/// game_version = "1.0.0"
/// api_version = 1
/// ```
///
/// # Remarks
///
/// The Game Module binary may contain additional metadata, including metadata already detailed
/// in the manifest, in certain circumstances.
///
/// Future `GameManifest` versions are guaranteed to be backwards compatible with this version
/// (i.e., future version may only add additional fields, they may not modify/remove pre-existing
/// fields). To further support compatibility, Unicard runtimes are required to ignore additional,
/// unexpected fields (so they can load future `GameManifest`s, which contain additional fields).
///
/// Game Module developers should not add their own custom fields, as such fields may be
/// used in future Unicard versions.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename = "manifest")]
pub struct GameManifest {
    /// The primary information about the Game Module.
    pub info: GameInfo,
}

/// The primary information about a Game Module.
///
/// # TOML format
///
/// An `info` table contains the following fields:
///
/// * An `id` field which holds a (random) 128-bit integer hex string (e.g., `A12732B81932739`).
///   This **must** match the value provided by the WASM binary. This string can contain
///   leading zeroes, although doing so is not necessary.
///
/// * A `name` field which holds a string value containing the name of the associated Game Module.
///
/// * A `game_version` field which holds a [`GameVersion`] string value (e.g., `1.0.0`). This
///   **must** match the value provided by the WASM binary.
///
/// * An `api_version` field which holds the Unicard API version number the Game Module
///   uses. This **must** match the value provided by the WASM binary.
///
/// # Examples
///
/// ```toml
/// [info]
/// id = "1EE974C21F4002475D23194DE3B641CF"
/// name = "example"
/// game_version = "2.1.0"
/// api_version = 1
/// ```
///
/// ```toml
/// info = {
///     id = "2A9D41B7763C3ED87B2EAD3AFAF793FB",
///     name = "example",
///     game_version = "1.2.0",
///     api_version = 1
/// }
/// ```
///
/// # Remarks
///
/// Astute users may realise that the Game Module binary also contains functions which return
/// the values of the game id, game version, and API version fields respectively -- the purpose of
/// the `id`, `game_version`, and `api_version` fields is to provide a way for the runtime to
/// determine version compatibility without having to compile and instantiate the binary, and
/// execute these functions (as doing so can be expensive).
///
/// Runtimes may impose additional restrictions on the `name` field (e.g., maximum length,
/// forbidden characters, etc), and may sanitise `name`s which do not comply with them.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename = "info")]
pub struct GameInfo {
    /// The unique identifier of the Game Module.
    ///
    /// The purpose of this field is to uniquely identify a card game implementation, allowing
    /// players to determine if they are using the same game implementation.
    ///
    /// For example, there might be two implementations of the card game Rummy (which are
    /// incompatible with each other) -- the `id` field will allow the players to determine
    /// whether they are using the _same_ implementation of Rummy, avoiding any
    /// difficult to understand compatibility errors.
    ///
    /// # Rules
    ///
    /// The unique identifier should:
    ///
    /// * Be randomly generated (due to the width of a 128-bit integer, it is safe to
    ///   assume a randomly generated 128-bit integer will be unique).
    ///
    /// * Not be copied from another Game Module, even if (the following list is not exhaustive):
    ///   * Both Game Modules implement the same card game.
    ///   * Both Game Modules were created by the same developer.
    ///   * One Game Module is a fork of the other[^1].
    ///
    /// * Not be changed (even if the Game Module receives a major update) -- to notify players
    ///   of a breaking change, modify the `game_version` field instead. (This rule only holds if
    ///   the Game Module implements the same card game both _before_ and _after_ the major change
    ///   -- if the Game Module is modified such that it implements a _different_ card game, it is
    ///   considered a new Game Module, not a modification, and the unique identifier should be
    ///   regenerated.)
    ///
    /// # Security
    ///
    /// It is possible for a malicious user to deliberately copy the unique identifier of another
    /// Game Module (e.g., to cause inconvenience to the players of the Game Module) -- as a result,
    /// the uniqueness of the unique identifier should not be relied upon as a safety or security
    /// invariant.
    ///
    /// # Remarks
    ///
    /// This **must** match the value provided by the Game Module's WASM binary.
    ///
    /// [^1]: Unless the fork is officially and publicly considered a transference of ownership
    ///       of the Game Module implementation.
    pub id: GameId,

    /// The name of the Game Module.
    ///
    /// # Remarks
    ///
    /// This field does not have to be unique (i.e., two separate users can develop two entirely
    /// different implementations of the same card game).
    ///
    /// This field can contain any valid Unicode character, although implementations are allowed
    /// to remove characters (e.g., trim whitespace, remove control characters, etc).
    pub name: String,

    /// The version of the Game Module.
    ///
    /// The purpose of this field is to determine the compatibility between two versions of the
    /// <u>same</u> Game Module implementation (e.g., if the user fixes a bug in their Game Module,
    /// is the patched version compatible with the un-patched version).
    ///
    /// # Security
    ///
    /// As with all other `info` fields, there is no security mechanism in place to ensure this
    /// field is used correctly (e.g., a breaking update without a major version bump, a new
    /// update with the same `game_version` as the previous update, etc) and, as a result, should
    /// not be relied upon as a safety or security invariant.
    ///
    /// # Remarks
    ///
    /// If a Game Module is modified such that it represents a different card game (rather than a
    /// new version of a pre-existing game implementation), the `id` should be re-generated
    /// (instead of updating the Game Module version).
    ///
    /// This **must** match the game version provided by the Game Module's binary.
    ///
    /// This field should receive a major version bump if the Game Module is updated to support a
    /// different version of the Unicard API.
    ///
    /// See [`GameVersion`] for more information.
    pub game_version: GameVersion,

    /// The API version of the WASM module.
    ///
    /// # Security
    ///
    /// As with all other `info` fields, there are no security mechanisms in place to
    /// ensure that the `api_version` is valid (e.g., that it matches the binary) and, as a result,
    /// it should not be relied upon as a safety or security invariant.
    ///
    /// # Remarks
    ///
    /// There are **no** compatibility guarantees between Unicard API versions (e.g., just because
    /// a Game Module complies with Unicard API version 1 does not mean it is compliant with
    /// Unicard API version 2, and vice-versa).
    ///
    /// The `game_version` field should receive a major version bump if a Game Module is modified
    /// to support a different version of the Unicard API (i.e., if this field is changed,
    /// the `game_version` field should receive a major version bump).
    ///
    /// This **must** match the API version provided by the Game Module's binary.
    pub api_version: ApiVersion,
}

impl GameModule {
    /// The name of [manifest file](GameModule#format) within the Game Module zip file.
    pub const MANIFEST_NAME: &'static str = "manifest.toml";

    /// The maximum size of the manifest file, in bytes.
    pub const MANIFEST_SIZE_MAX: u32 = 1 << 14;

    /// The name of the [binary file](GameModule#format) within the Game Module zip file.
    pub const BINARY_NAME: &'static str = "binary";

    /// The maximum size of the binary file, in bytes.
    pub const BINARY_SIZE_MAX: u32 = 1 << 24;

    /// Create a new Game Module from a Unicard Game Module file.
    ///
    /// See [GameModule#format] for the format of a Game Module file.
    ///
    /// # Remarks
    ///
    /// This operation is expensive, as it involves compiling the WASM binary contained within
    /// the Unicard Game Module. If you require a quick extraction of the [`GameManifest`]
    /// contained within the Unicard Game Module, see [`GameManifest::from_module_file`] instead.
    ///
    /// If the Game Module file targets an unsupported version of the Unicard API, it will
    /// return an error: even though it is perfectly possible for an unsupported Game Module
    /// to be loaded, there is little point in wasting memory and time compiling a WASM binary
    /// that will never be instantiated.
    ///
    /// If you want to read the manifest from a Unicard Game Module, even if the Game Module
    /// targets an unsupported API, see [`GameManifest::from_module_file`].
    pub fn new(module_file: impl Read + Seek) -> Result<Self, InvalidGameModuleError> {
        let mut module_archive = match ZipArchive::new(module_file) {
            Ok(archive) => archive,
            Err(zip_error) => {
                return Err(InvalidGameModuleError::from_zip_error_no_file(zip_error)
                    // `from_zip_error_no_file` only returns `None` if `zip_error` is
                    // `ZipError::FileNotFound`, which isn't possible when opening an archive
                    // (as we aren't searching for a file!)
                    .expect("no file is being searched for"));
            }
        };

        // Read the manifest
        let manifest: GameManifest = {
            let manifest_file = match module_archive.by_name(Self::MANIFEST_NAME) {
                Ok(file) => file,
                Err(zip_error) => {
                    return Err(InvalidGameModuleError::from_zip_error_no_file(zip_error)
                        .unwrap_or(InvalidGameModuleError::MissingManifest))
                }
            };

            let size = manifest_file.size();
            if size > (Self::MANIFEST_SIZE_MAX as u64) {
                return Err(InvalidGameModuleError::ManifestTooLarge);
            }

            // NOTE: `Self::MANIFEST_SIZE_MAX` is guaranteed to be below `2^32`, meaning it should
            //       always be convertible to a `usize` (assuming `usize` is at least 32 bits).
            let mut manifest_string = String::with_capacity(size as usize);

            // NOTE: `take` is required here to prevent `manifest_file.size()` from being
            //       incorrect (e.g., setting the size to `1` byte and supplying a `1GiB` file)
            match manifest_file
                .take(size)
                .read_to_string(&mut manifest_string)
            {
                Ok(_) => (),
                Err(io_error) => return Err(InvalidGameModuleError::Io(io_error)),
            }

            match toml::from_str(&manifest_string) {
                Ok(manifest) => manifest,
                Err(error) => {
                    return Err(InvalidGameModuleError::InvalidManifest(
                        InvalidManifestError { inner: error },
                    ))
                }
            }
        };

        // If the Game Module targets an unsupported version of the Unicard API, there is little
        // point loading and compiling the Game Module, as the user will never be able to
        // instantiate it
        if !manifest.is_supported() {
            return Err(InvalidGameModuleError::UnsupportedUnicardApi);
        }

        let binary_bytes: Vec<u8> = {
            let binary_file = match module_archive.by_name(Self::BINARY_NAME) {
                Ok(file) => file,
                Err(zip_error) => {
                    return Err(InvalidGameModuleError::from_zip_error_no_file(zip_error)
                        .unwrap_or(InvalidGameModuleError::MissingBinary))
                }
            };

            let size = binary_file.size();
            if size > (Self::MANIFEST_SIZE_MAX as u64) {
                return Err(InvalidGameModuleError::BinaryTooLarge);
            }

            // NOTE: `Self::MANIFEST_SIZE_MAX` is guaranteed to be below `2^32`, meaning it should
            //       always be convertible to a `usize` (assuming `usize` is at least 32 bits).
            let mut binary_bytes = Vec::with_capacity(size as usize);

            // NOTE: `take` is required here to prevent `manifest_file.size()` from being
            //       incorrect (e.g., setting the size to `1` byte and supplying a `1GiB` file)
            match binary_file.take(size).read_to_end(&mut binary_bytes) {
                Ok(_) => (),
                Err(io_error) => return Err(InvalidGameModuleError::Io(io_error)),
            }

            binary_bytes
        };

        Self::from_parts(manifest, binary_bytes)
    }

    /// Create a `GameModule` from its individual components.
    ///
    /// # Remarks
    ///
    /// This is an expensive operation and should only be performed if necessary.
    #[inline]
    pub fn from_parts(
        manifest: GameManifest,
        binary_bytes: impl AsRef<[u8]>,
    ) -> Result<Self, InvalidGameModuleError> {
        let engine = Default::default();
        let module = match Module::new(&engine, binary_bytes) {
            Ok(module) => module,
            Err(error) => {
                return Err(InvalidGameModuleError::InvalidWasmBinary(
                    InvalidWasmBinaryError { inner: error },
                ))
            }
        };

        Ok(Self { manifest, module })
    }

    /// The manifest of the Game Module.
    #[inline]
    pub fn manifest(&self) -> &GameManifest {
        &self.manifest
    }
}

impl GameManifest {
    /// Retrieve the `GameManifest` from a [Game Module file](GameModule#format).
    ///
    /// The purpose of this function is to allow a manifest file to be loaded without loading
    /// the corresponding binary (which could be several hundred mebibytes in size). This allows
    /// large numbers of manifest to be loaded (e.g., for a selection screen) without needlessly
    /// wasting resources for the binary files.
    ///
    /// # Remarks
    ///
    /// This function will load Game Modules which target unsupported Unicard APIs (i.e., it
    /// will never return [`InvalidGameModuleError::UnsupportedUnicardApi`]).
    /// To check if the associated Game Module targets a supported Unicard API,
    /// see [`GameManifest::is_supported`].
    pub fn from_module_file(module_file: impl Read + Seek) -> Result<Self, InvalidGameModuleError> {
        let mut zip_archive = match ZipArchive::new(module_file) {
            Ok(zip_archive) => zip_archive,
            Err(zip_error) => {
                return Err(InvalidGameModuleError::from_zip_error_no_file(zip_error)
                    // `from_zip_error_no_file` only returns `None` if `zip_error` is
                    // `ZipError::FileNotFound`, which isn't possible when opening an archive
                    // (as we aren't searching for a file!)
                    .expect("no file is being searched for"));
            }
        };

        let manifest_file = match zip_archive.by_name(GameModule::MANIFEST_NAME) {
            Ok(manifest_file) => manifest_file,
            Err(zip_error) => {
                return Err(InvalidGameModuleError::from_zip_error_no_file(zip_error)
                    .unwrap_or(InvalidGameModuleError::MissingManifest))
            }
        };

        let size = manifest_file.size();
        if size > (GameModule::MANIFEST_SIZE_MAX as u64) {
            return Err(InvalidGameModuleError::ManifestTooLarge);
        }

        let mut manifest_string = String::with_capacity(size as usize);

        // NOTE: `take` is required here to prevent malformed/malicious zip files from lying
        //       about their uncompressed size (e.g., providing a value of `1` byte, then providing
        //       a `10` GiB file).
        match manifest_file
            .take(size)
            .read_to_string(&mut manifest_string)
        {
            Ok(_) => (),
            Err(io_error) => return Err(InvalidGameModuleError::Io(io_error)),
        }

        match toml::from_str(&manifest_string) {
            Ok(manifest) => Ok(manifest),
            Err(toml_error) => Err(InvalidGameModuleError::InvalidManifest(
                InvalidManifestError { inner: toml_error },
            )),
        }
    }

    /// Check whether the Game Module the `GameManifest` is associated with targets a supported
    /// Unicard API.
    ///
    /// The result of this function is guaranteed to be equal to the result of
    /// [`self.info.api_version.is_supported()`](ApiVersion::is_supported):
    ///
    /// ```rust
    /// # /*
    /// use std::fs::File;
    /// # */
    /// use unicard_core::module::GameManifest;
    /// # use unicard_core::module::*;
    /// # /*
    ///
    /// let game_manifest_file = File::open("my_module.ugm").unwrap();
    /// let game_manifest = GameManifest::from_game_module(game_manifest_file).unwrap();
    /// # */
    /// # let game_manifest = GameManifest {
    /// #     info: GameInfo {
    /// #         id: GameId::from_u128(1),
    /// #         name: String::new(),
    /// #         api_version: ApiVersion::from_u32(1).unwrap(),
    /// #         game_version: GameVersion::from_tuple((1, 0, 0))
    /// #     }
    /// # };
    ///
    /// assert_eq!(game_manifest.is_supported(), game_manifest.info.api_version.is_supported());
    /// ```
    #[inline]
    pub fn is_supported(&self) -> bool {
        self.info.api_version.is_supported()
    }
}

/// The 128-bit unique identifier of a [Game Module](GameModule).
///
/// The purpose of the unique identifier is to allow multiple implementations of the same card game
/// (e.g., two incompatible, but correct, implementations of the card game President). See
/// [`GameInfo::id`] for more information.
///
/// # Rules
///
/// The unique identifier should:
///
/// * Be randomly generated (due to the width of a 128-bit integer, a randomly generated `GameId`
///   is practically guaranteed to be unique).
///
/// * Not be copied from another Game Module, even if:
///   * The Game Modules implement the same card game (e.g., they both implement Rummy).
///   * The Game Modules were created by the same developer.
///   * One Game Module is a fork of the other[^1].
///
/// * Be immutable, even if the Game Module is updated in an incompatible way (i.e., such that
///   a previous version of the Game Module is incompatible with the new version). It should be
///   noted that, if the Game Module is changed to implement a _different_ card game (e.g.,
///   if a pre-existing Game Module is used as a template), then it should be considered a new (and
///   unrelated) Game Module and the unique identifier should be regenerated as a result.
///
/// # Security
///
/// There are no security mechanisms in place to ensure that a unique identifier is unique (e.g.,
/// that it hasn't been copied from another Game Module). As a result, the uniqueness of the
/// unique identifier should **not** be relied upon as a safety or security invariant.
///
/// # Format
///
/// The serde format of `GameId` is the underlying `u128` converted to a capitalised hexadecimal
/// string.
///
/// [^1]: Unless the fork is publicly and officially understood to be a transference of
///       ownership of the original Game Module.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GameId(u128);

impl GameId {
    /// Create a new Game Module ID from a `u128`.
    #[inline]
    pub fn from_u128(id: u128) -> Self {
        Self(id)
    }

    /// Retrieve the inner `u128`.
    #[inline]
    pub fn to_u128(self) -> u128 {
        self.0
    }
}

impl From<u128> for GameId {
    #[inline]
    fn from(id: u128) -> Self {
        Self::from_u128(id)
    }
}

impl From<GameId> for u128 {
    #[inline]
    fn from(game_id: GameId) -> Self {
        game_id.to_u128()
    }
}

impl Display for GameId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}", self.0)
    }
}

impl Serialize for GameId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

// NOTE: `#[serde(TryFrom = "&str", Into = "String")]` was tried initially, however, the `toml`
// crate only supported owned strings for `TryFrom` (which seemed like an unnecessary tradeoff)
impl<'de> Deserialize<'de> for GameId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct GameIdVisitor;

        impl<'de> Visitor<'de> for GameIdVisitor {
            type Value = GameId;

            fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
                formatter.write_str("a unique Game identifier")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                match u128::from_str_radix(v, 16) {
                    Ok(id_num) => Ok(GameId(id_num)),
                    Err(error) => match *error.kind() {
                        IntErrorKind::InvalidDigit => {
                            Err(E::invalid_value(Unexpected::Str(v), &self))
                        }
                        IntErrorKind::PosOverflow => Err(E::custom(
                            "unique identifier does not fit into a 128-bit integer",
                        )),
                        IntErrorKind::NegOverflow => Err(E::custom(
                            "unique Game identifier needs to be an unsigned integer",
                        )),
                        IntErrorKind::Empty => Err(E::invalid_value(Unexpected::Str(v), &self)),

                        // We are not parsing a `NonZeroU*` numeric
                        IntErrorKind::Zero => unreachable!(),

                        // enum is non_exhaustive
                        _ => Err(E::invalid_value(Unexpected::Str(v), &self)),
                    },
                }
            }
        }

        deserializer.deserialize_str(GameIdVisitor)
    }
}

/// A Unicard API version.
///
/// This specifies the version of the Unicard API the WASM binary implements.
///
/// # Purpose
///
/// It is difficult to design a flawless API, especially during the first few attempts.
/// `ApiVersion` exists to allow new, improved (and likely incompatible) Unicard API versions
/// to be developed whilst preserving the ability to run older Game Modules (which use the older
/// API versions).
///
/// `ApiVersion` does this by recording the version number of the Unicard API the Game Module
/// conforms to: this allows for incompatibilities (e.g., where a runtime does not support a
/// specific Unicard API version) to be detected early and for the runtime to load specific
/// Unicard API version Game Module executors (e.g., a runtime might have a `v1` executor for
/// `v1` Game Modules, and a `v2` executor for `v2` Game Modules).
///
/// # Backwards Compatibility
///
/// `ApiVersion` makes no backwards compatibility guarantees (meaning a `v2` Game Module
/// may not run on a `v1` runtime, and vice-versa). The only guarantee is that a runtime and
/// Game Module which both target the same `ApiVersion` are guaranteed to be compatible, and that
/// all Game Modules expose an `api_version() -> u32` function, irrespective of Unicard API
/// version.
///
/// # Serde Format
///
/// The serde format of an `ApiVersion` is the Unicard API version number it represents.
///
/// # Remarks
///
/// Upgrading a Game Module to a newer `ApiVersion` is considered a breaking change, and therefore
/// requires a major version bump.
///
/// To facilitate easy API compatibility checks, the versioning API is guaranteed to be the
/// same across **all** Unicard API versions (i.e., that all compliant Game Module binaries
/// must have the `api_version` function, irrespective of the Unicard API version they conform
/// to).
///
/// Providing an incorrect `ApiVersion` will likely cause the Game Module to break (as the runtime
/// will interact with it differently).
// NOTE: a struct was used instead of an enum as it is impossible to have an exhaustive list
//       of all Unicard API versions, even at compile time, as the program may have been
//       written before a new Unicard API version is released
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq)]
#[serde(transparent)]
pub struct ApiVersion(pub NonZeroU32);

impl ApiVersion {
    /// Create a new `ApiVersion` from a `u32` Unicard API version number.
    ///
    /// `api_version_num` must be non-zero.
    ///
    /// # Returns
    ///
    /// [`Ok(ApiVersion)`](Ok) if `api_version_num` is a valid API version number (i.e., is
    /// not `0`), [`Err`] otherwise.
    #[inline]
    pub fn from_u32(api_version_num: u32) -> Result<Self, InvalidApiVersionError> {
        let api_version_num = match NonZeroU32::new(api_version_num) {
            Some(api_version_num) => api_version_num,
            None => return Err(InvalidApiVersionError),
        };

        Ok(Self(api_version_num))
    }

    /// Retrieve the Unicard API version number.
    #[inline]
    pub fn to_u32(self) -> u32 {
        self.0.get()
    }

    /// Whether this crate supports the Unicard API version.
    #[inline]
    pub fn is_supported(self) -> bool {
        match self.0.get() {
            0 => unreachable!("`self.0` is a `NonZeroU32`, therefore value cannot be `0`"),
            1 => true,
            _ => false,
        }
    }
}

impl From<NonZeroU32> for ApiVersion {
    #[inline]
    fn from(api_version_num: NonZeroU32) -> Self {
        Self(api_version_num)
    }
}

impl From<ApiVersion> for NonZeroU32 {
    #[inline]
    fn from(api_version: ApiVersion) -> Self {
        api_version.0
    }
}

impl TryFrom<u32> for ApiVersion {
    type Error = InvalidApiVersionError;

    #[inline]
    fn try_from(api_version_num: u32) -> Result<Self, Self::Error> {
        Self::from_u32(api_version_num)
    }
}

impl From<ApiVersion> for u32 {
    #[inline]
    fn from(api_version: ApiVersion) -> Self {
        api_version.to_u32()
    }
}

impl Display for ApiVersion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_char('V')?;
        self.to_u32().fmt(f)
    }
}

/// An invalid Unicard API version number was provided.
///
/// The only invalid Unicard API version is `0` -- all other `u32` values are valid (even if
/// the Unicard API version hasn't been released yet!)
///
/// # Remarks
///
/// The reason unreleased Unicard API versions are valid is due to the inability to verify the
/// existence of a Unicard API version: in order for such a check to be possible, a centralised
/// web server containing all Unicard API versions would need to be created, and a request
/// sent to that server to verify the API version, which brings privacy, maintainability, and
/// accessibility concerns.
///
/// With the current solution (where all Unicard API versions, except `0`, are valid), the worst
/// thing that can happen is the user provides an unreleased Unicard API version number, and gets
/// told that the Game Module is unsupported.
#[derive(Debug, Copy, Clone)]
pub struct InvalidApiVersionError;

impl Display for InvalidApiVersionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("invalid Unicard API version")
    }
}

impl std::error::Error for InvalidApiVersionError {}

/// The version of a [Game Module](GameModule).
///
/// This behaves almost identically to the [semantic versioning scheme], with the exception of
/// pre-release and build metadata, which are not supported.
///
/// The purpose of this struct is to determine the compatibility between two different updates
/// of a Game Module -- this ensures that users don't accidentally use two incompatible Game Module
/// versions together, and that they are presented with an easy-to-understand compatibility
/// error explaining the issue if they do.
///
/// # Compatibility
///
/// Compatibility calculations are done from the server's point of view -- two Game Module's
/// are compatible if the client's version is compatible (forwards or backwards) with the server's
/// version.
///
/// Examples:
///
/// | Client | Server | Compatible? |
/// |--------|--------|-------------|
/// |  1.0.0 |  1.0.2 |     Yes     |
/// | 1.0.47 |  1.0.2 |     Yes     |
/// |  1.2.3 |  1.0.2 |     Yes     |
/// |  0.3.5 |  0.3.4 |     Yes     |
/// |  1.0.2 |  1.2.3 |      No     |
/// |  0.3.4 |  0.3.5 |      No     |
/// |  2.0.0 |  1.9.5 |      No     |
/// |  1.9.5 |  2.0.0 |      No     |
///
///
/// The two primary reasons compatibility is determined from the server's POV are:
///
/// 1. The majority of the logic is done on the server.
/// 2. There is only one server, whereas there can be several clients (it is easier to reason about
///    as only one version check needs to be done).
///
/// # Serde Format
///
/// The way `GameVersion` is formatted is dependent on the serialiser/deserialiser:
///
/// * For a human-readable (de)serialiser, the serde format of `GameVersion` is a string equal
///   to `GameVersion::to_string` (`"X.Y.Z"`, where `X`, `Y`, and `Z` are the major, minor, and
///   patch version numbers respectively).
///
/// * For a compact (de)serialiser, the serde format of `GameVersion` is a tuple composed of `3`
///   `u32`s: the major version number, the minor version number, and the patch version number.
///
/// # Tuple Format
///
/// `GameVersion` can be converted to a tuple of `3` [`u32`]s -- the tuple takes the following
/// format: `(major, minor, patch)`.
///
/// [semantic versioning scheme]: https://semver.org/
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GameVersion {
    /// The major version number.
    ///
    /// This is analogous to the major version number in the [semantic versioning scheme].
    ///
    /// [semantic versioning scheme]: https://semver.org/
    pub major: u32,

    /// The minor version number.
    ///
    /// This is analogous to the minor version number in the [semantic versioning scheme].
    ///
    /// [semantic versioning scheme]: https://semver.org/
    pub minor: u32,

    /// The patch version number.
    ///
    /// This is analogous to the patch version number in the [semantic versioning scheme].
    ///
    /// [semantic versioning scheme]: https://semver.org/
    pub patch: u32,
}

impl GameVersion {
    /// Create a `GameVersion` from a tuple of `3` [`u32`]s.
    ///
    /// The tuple should be in the following format: `(major, minor, patch)`.
    #[inline]
    pub fn from_tuple(tuple: (u32, u32, u32)) -> Self {
        Self {
            major: tuple.0,
            minor: tuple.1,
            patch: tuple.2,
        }
    }

    /// Convert a `GameVersion` into a tuple of `3` [`u32`]s.
    ///
    /// The tuple will be in the following format: `(major, minor, patch)`.
    #[inline]
    pub fn to_tuple(self) -> (u32, u32, u32) {
        (self.major, self.minor, self.patch)
    }
}

impl From<(u32, u32, u32)> for GameVersion {
    #[inline]
    fn from(tuple: (u32, u32, u32)) -> Self {
        Self::from_tuple(tuple)
    }
}

impl From<GameVersion> for (u32, u32, u32) {
    #[inline]
    fn from(game_version: GameVersion) -> Self {
        game_version.to_tuple()
    }
}

impl Display for GameVersion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl Serialize for GameVersion {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&format!("{}", self))
        } else {
            let mut tuple = serializer.serialize_tuple(3)?;
            tuple.serialize_element(&self.major)?;
            tuple.serialize_element(&self.minor)?;
            tuple.serialize_element(&self.patch)?;
            tuple.end()
        }
    }
}

impl<'de> Deserialize<'de> for GameVersion {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct GameVersionReadableVisitor;
        impl<'de> Visitor<'de> for GameVersionReadableVisitor {
            type Value = GameVersion;

            fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
                formatter.write_str("version string `X.Y.Z`")
            }

            fn visit_str<E>(self, original: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                fn invalid_val<T, E: serde::de::Error>(
                    vis: &GameVersionReadableVisitor,
                    v: &str,
                ) -> Result<T, E> {
                    Err(E::invalid_value(Unexpected::Str(v), vis))
                }

                // A version number can only be composed of the digits 0-9 and a `.`,  which
                // are all ASCII characters (therefore any non-ASCII string is an invalid
                // version number).
                if !original.is_ascii() {
                    return invalid_val(&self, original);
                }

                let ascii_str = original.as_bytes();

                // Major
                let Ok((major, ascii_str)) = numeric_identifier(ascii_str) else {
                    return invalid_val(&self, original);
                };
                let Ok(ascii_str) = dot(ascii_str) else {
                    return invalid_val(&self, original);
                };

                // Minor
                let Ok((minor, ascii_str)) = numeric_identifier(ascii_str) else {
                    return invalid_val(&self, original);
                };
                let Ok(ascii_str) = dot(ascii_str) else {
                    return invalid_val(&self, original);
                };

                // Patch
                let Ok((patch, ascii_str)) = numeric_identifier(ascii_str) else {
                    return invalid_val(&self, original);
                };

                if !ascii_str.is_empty() {
                    return invalid_val(&self, original);
                }

                Ok(GameVersion {
                    major,
                    minor,
                    patch,
                })
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(GameVersionReadableVisitor)
        } else {
            let game_version_tuple: (u32, u32, u32) = Deserialize::deserialize(deserializer)?;
            Ok(core::convert::Into::<GameVersion>::into(game_version_tuple))
        }
    }
}

/// Retrieve the next `u32` in an ASCII string.
///
/// Stolen from the `semver` crate.
///
/// # Returns
///
/// `Err` if there is a leading zero or there are no digits to parse.
fn numeric_identifier(ascii_str: &[u8]) -> Result<(u32, &[u8]), ()> {
    let mut len = 0usize;
    let mut value = 0u32;

    // Shamelessly stolen from the `semver` crate
    while let Some(&digit) = ascii_str.get(len) {
        if !digit.is_ascii_digit() {
            break;
        }
        if value == 0 && len > 0 {
            return Err(());
        }
        match value
            .checked_mul(10)
            .and_then(|value| value.checked_add((digit - b'0') as u32))
        {
            Some(sum) => value = sum,
            None => return Err(()),
        }
        len += 1;
    }

    if len > 0 {
        Ok((value, &ascii_str[len..]))
    } else {
        Err(())
    }
}

/// Strip `ascii_str` of a `.`.
///
/// Idea stolen from the `semver` crate.
fn dot(ascii_str: &[u8]) -> Result<&[u8], ()> {
    if let Some(rest) = ascii_str.strip_prefix(b".") {
        Ok(rest)
    } else {
        Err(())
    }
}

/// The [Game Module file](GameModule#format) was invalid.
#[derive(Debug)]
pub enum InvalidGameModuleError {
    /// There was an IO error whilst reading the file.
    ///
    /// # Remarks
    ///
    /// Whilst not technically an issue with the Game Module file's format, it is still pertinent,
    /// given the only way to avoid an IO error would be to load the entire file into memory,
    /// which is impractical, expensive, and sometimes not even possible.
    Io(io::Error),

    /// The underlying zip archive is invalid.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    InvalidZip,

    /// The underlying zip archive is unsupported.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    ///
    /// # Remarks
    ///
    /// Causes for this vary, but include:
    ///
    /// * An unsupported compression algorithm being used (even if officially listed in the
    ///   zip specification).
    ///
    /// * An unsupported feature being used (e.g., zip64).
    UnsupportedZip,

    /// The underlying zip archive is encrypted.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    ///
    /// # Remarks
    ///
    /// Encrypted Game Module files are generally not supported (as there is very few
    /// legitimate reasons for them to exist).
    EncryptedZip,

    /// The `manifest.toml` file is missing from the zip archive.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    MissingManifest,

    /// The `binary` file is missing from the zip archive.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    MissingBinary,

    /// The `manifest.toml` file is too large.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    ///
    /// # Remarks
    ///
    /// Unicard runtimes are free to impose size restrictions on the inner files to prevent
    /// resource overuse (e.g., an attacker providing a massive file with the intent of
    /// consuming too much memory and freezing the victim's computer). This error occurs
    /// when the manifest file is larger than what can reasonably be expected.
    ManifestTooLarge,

    /// The `binary` file is too large.
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    ///
    /// # Remarks
    ///
    /// Unicard runtimes are free to impose size restrictions on the inner files to prevent
    /// resource overuse (e.g., an attacker providing a massive file with the intent of
    /// consuming too much memory and freezing the victim's computer). This error occurs
    /// when the binary file is larger than what can reasonably be expected.
    BinaryTooLarge,

    /// The `manifest.toml` file is invalid (e.g., invalid TOML, invalid value, etc).
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    InvalidManifest(InvalidManifestError),

    /// The `binary` file is invalid (e.g., invalid WASM).
    ///
    /// A Game Module file is, put simply, a zip archive with a few files.
    ///
    /// # Remarks
    ///
    /// Some Unicard runtimes may not support WAT (WebAssembly Text format) -- developers should
    /// ensure a Unicard runtime supports WAT before attempting to waste their time and
    ///  find the syntax error in the `binary` file.
    InvalidWasmBinary(InvalidWasmBinaryError),

    /// The `binary` file targets an unsupported version of the Unicard API.
    UnsupportedUnicardApi,
}

impl InvalidGameModuleError {
    /// Converts a [`ZipError`] to an `InvalidModuleError`.
    ///
    /// # Returns
    ///
    /// [`Some(InvalidModuleError)`](Some) for all [`ZipError`] variants **except**
    /// [`ZipError::FileNotFound`], for which [`None`] will be returned (due to the nature of
    /// `InvalidModuleError`, which does not have a 1:1 equivalent).
    fn from_zip_error_no_file(error: ZipError) -> Option<Self> {
        Some(match error {
            ZipError::Io(error) => Self::Io(error),
            ZipError::InvalidArchive(_) => Self::InvalidZip,
            ZipError::UnsupportedArchive(ZipError::PASSWORD_REQUIRED) => Self::EncryptedZip,
            ZipError::UnsupportedArchive(_) => Self::UnsupportedZip,
            ZipError::FileNotFound => return None,
        })
    }
}

impl Display for InvalidGameModuleError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use InvalidGameModuleError as Err;

        f.write_str("invalid game module error: ")?;

        match self {
            Err::Io(_) => f.write_str("an io error occurred"),
            Err::InvalidZip => f.write_str("invalid zip archive"),
            Err::UnsupportedZip => f.write_str("unsupported zip archive format"),
            Err::EncryptedZip => f.write_str("zip archive is encrypted"),
            Err::MissingManifest => write!(
                f,
                "zip archive missing manifest file `{}`",
                GameModule::MANIFEST_NAME
            ),
            Err::MissingBinary => write!(
                f,
                "zip archive missing WASM binary file `{}`",
                GameModule::BINARY_NAME
            ),
            Err::ManifestTooLarge => write!(
                f,
                "zip archive manifest file exceeded maximum size of `{}`",
                GameModule::MANIFEST_SIZE_MAX
            ),
            Err::BinaryTooLarge => write!(
                f,
                "zip archive binary file exceeded maximum size of `{}`",
                GameModule::MANIFEST_SIZE_MAX
            ),
            Err::InvalidManifest(_) => f.write_str("the manifest is invalid"),
            Err::InvalidWasmBinary(_) => f.write_str("the inner WASM binary is invalid"),
            Err::UnsupportedUnicardApi => f.write_str("unsupported unicard API version"),
        }
    }
}

impl std::error::Error for InvalidGameModuleError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use InvalidGameModuleError as Err;

        match self {
            Err::Io(error) => Some(error),
            Err::InvalidManifest(error) => Some(error),
            Err::InvalidWasmBinary(error) => Some(error),
            _ => None,
        }
    }
}

/// The [`manifest.toml`](GameManifest) file within the [Game Module](GameModule#format) is invalid.
///
/// Reasons for this error include (this list is non-exhaustive):
///
/// * Invalid TOML.
/// * Invalid values (e.g., provided a number instead of a string).
#[derive(Debug)]
pub struct InvalidManifestError {
    inner: toml::de::Error,
}

impl Display for InvalidManifestError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl std::error::Error for InvalidManifestError {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        Some(&self.inner)
    }
}

/// The binary file within the [Game Module file](GameModule#format) is invalid.
///
/// # Remarks
///
/// Not all Unicard runtimes support the use of WAT (WebAssembly Text format) -- Game Module
/// developers should ensure the Unicard runtime supports WAT before attempting to use it
/// with said runtime. Production Game Modules should **always** be compiled.
#[derive(Debug)]
pub struct InvalidWasmBinaryError {
    inner: Error,
}

impl Display for InvalidWasmBinaryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl std::error::Error for InvalidWasmBinaryError {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        Some(self.inner.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_test::{assert_de_tokens, assert_tokens, Configure, Token};

    #[test]
    fn gv_read_ser() {
        fn t(tup: (u32, u32, u32), s: &'static str) {
            let game_ver: GameVersion = tup.into();
            assert_tokens(&game_ver.readable(), &[Token::Str(s)]);
        }

        t((1, 23, 23), "1.23.23");
        t((0, 23, 45), "0.23.45");
        t((0, 0, u32::MAX), "0.0.4294967295");
    }

    #[test]
    fn gv_comp_ser() {
        fn t(tup: (u32, u32, u32)) {
            let game_ver: GameVersion = tup.into();
            assert_tokens(
                &game_ver.compact(),
                &[
                    Token::Tuple { len: 3 },
                    Token::U32(tup.0),
                    Token::U32(tup.1),
                    Token::U32(tup.2),
                    Token::TupleEnd,
                ],
            );
        }

        t((1, 23, 23));
        t((0, 23, 45));
        t((0, 0, u32::MAX));
    }

    fn gv_deser_invalid(tup: (u32, u32, u32), str: &'static str) {
        // Game Version doesn't really matter
        let game_ver: GameVersion = tup.into();
        assert_de_tokens(&game_ver.readable(), &[Token::Str(str)]);
    }

    #[test]
    #[should_panic]
    fn gv_deser_leading() {
        gv_deser_invalid((1, 0, 0), "01.0.0");
    }

    #[test]
    #[should_panic]
    fn gv_deser_trailing() {
        gv_deser_invalid((1, 0, 0), "1.0.0hello");
    }

    #[test]
    #[should_panic]
    fn gv_deser_dot() {
        gv_deser_invalid((1, 2, 0), "1,2,0");
    }

    #[test]
    #[should_panic]
    fn gv_deser_start() {
        gv_deser_invalid((1, 0, 0), "v1.0.0");
    }

    #[test]
    #[should_panic]
    fn gv_deser_start2() {
        gv_deser_invalid((1, 0, 0), "a.0.0");
    }

    #[test]
    #[should_panic]
    fn gv_deser_negative() {
        gv_deser_invalid((1, 0, 0), "1.-1.0");
    }

    #[test]
    #[should_panic]
    fn gv_deser_overflow() {
        gv_deser_invalid((1, 0, 0), "1.0.11282179912739173123391291");
    }

    #[test]
    fn game_module_stream() {
        use std::io::Cursor;

        let mut zip_bytes = Vec::new();
        {
            use std::io::{Cursor, Write};
            use zip::{write::FileOptions, ZipWriter};

            let mut zip = ZipWriter::new(Cursor::new(&mut zip_bytes));
            let options = FileOptions::default();

            zip.start_file(GameModule::MANIFEST_NAME, options)
                .expect("failed to create manifest file");
            zip.write(
                br#"
                [info]
                id = "2A9D41B7763C3ED87B2EAD3FBDF793FB"
                name = "test"
                game_version = "1.0.0"
                api_version = 1
            "#,
            )
            .expect("failed to write manifest");

            zip.start_file(GameModule::BINARY_NAME, options)
                .expect("failed to create binary file");
            zip.write(b"(module)").expect("failed to write binary");

            zip.finish().expect("failed to write changes");
        }

        let game_module = GameModule::new(Cursor::new(&zip_bytes[..]))
            .expect("game module creation to be successful");

        assert_eq!(
            game_module.manifest().info.id,
            GameId::from_u128(0x2A9D41B7763C3ED87B2EAD3FBDF793FB)
        );
        assert_eq!(game_module.manifest().info.name, "test".to_string());
        assert_eq!(
            game_module.manifest().info.game_version,
            GameVersion::from_tuple((1, 0, 0))
        );
        assert_eq!(
            game_module.manifest().info.api_version,
            ApiVersion::from_u32(1).unwrap()
        );
    }

    #[test]
    fn game_module_stream_additional_fields() {
        use std::io::Cursor;

        let mut zip_bytes = Vec::new();
        {
            use std::io::{Cursor, Write};
            use zip::{write::FileOptions, ZipWriter};

            let mut zip = ZipWriter::new(Cursor::new(&mut zip_bytes));
            let options = FileOptions::default();

            zip.start_file(GameModule::MANIFEST_NAME, options)
                .expect("failed to create manifest file");
            // NOTE: Test that additional fields will be ignored for forwards compatibility
            // purposes
            zip.write(
                br#"
                [info]
                id = "2A9D41B7763C3ED87B2EAD3FBDF793FB"
                name = "test"
                game_version = "1.0.0"
                api_version = 1
                additional_field = "HELLO THERE!"

                [cheese]
                pizza = true

                [[my_thing]]
                a = 1

                [[my_thing]]
                a = 2
            "#,
            )
            .expect("failed to write manifest");

            zip.start_file(GameModule::BINARY_NAME, options)
                .expect("failed to create binary file");
            zip.write(b"(module)").expect("failed to write binary");

            zip.finish().expect("failed to write changes");
        }

        let game_module = GameModule::new(Cursor::new(&zip_bytes[..]))
            .expect("game module creation to be successful");

        assert_eq!(
            game_module.manifest().info.id,
            GameId::from_u128(0x2A9D41B7763C3ED87B2EAD3FBDF793FB)
        );
        assert_eq!(game_module.manifest().info.name, "test".to_string());
        assert_eq!(
            game_module.manifest().info.game_version,
            GameVersion::from_tuple((1, 0, 0))
        );
        assert_eq!(
            game_module.manifest().info.api_version,
            ApiVersion::from_u32(1).unwrap()
        );
    }

    #[test]
    fn game_module_stream_manifest_only() {
        use std::io::Cursor;

        let mut zip_bytes = Vec::new();
        {
            use std::io::{Cursor, Write};
            use zip::{write::FileOptions, ZipWriter};

            let mut zip = ZipWriter::new(Cursor::new(&mut zip_bytes));
            let options = FileOptions::default();

            zip.start_file(GameModule::MANIFEST_NAME, options)
                .expect("failed to create manifest file");
            zip.write(
                br#"
                [info]
                id = "2A9D41B7763C3ED87B2EAD3FBDF793FB"
                name = "test"
                game_version = "1.0.0"
                api_version = 5
            "#,
            )
            .expect("failed to write manifest");

            zip.start_file(GameModule::BINARY_NAME, options)
                .expect("failed to create binary file");
            zip.write(b"(module)").expect("failed to write binary");

            zip.finish().expect("failed to write changes");
        }

        let manifest = GameManifest::from_module_file(Cursor::new(&zip_bytes[..]))
            .expect("game module creation to be successful");

        assert_eq!(
            manifest.info.id,
            GameId::from_u128(0x2A9D41B7763C3ED87B2EAD3FBDF793FB)
        );
        assert_eq!(manifest.info.name, "test".to_string());
        assert_eq!(
            manifest.info.game_version,
            GameVersion::from_tuple((1, 0, 0))
        );
        assert_eq!(manifest.info.api_version, ApiVersion::from_u32(5).unwrap());
    }
}
