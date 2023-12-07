//! # Unicard Wasm Types
//!
//! This crate contains the Unicard types used in communication between the Unicard client and
//! the Unicard module instance (e.g., the configuration type used to communicate the configuration
//! settings for a particular card game). Additionally, it contains the traits necessary to
//! encode/decode these types into WASM32 memory.
//!
//! This crate is intended to be used by both Unicard client implementations and Unicard module
//! implementations, and has been designed accordingly.
//!
//! ## Format
//!
//! The WASM32 representation of Unicard Wasm Types (UWTs) generally follows the following format:
//!
//! * All formats are inline, even if they are dynamically sized, and do not make use of
//!   multiple allocations or indirection.
//!
//! * Dynamically sized types usually start with a `u32` describing the size of the type (e.g.,
//!   for a [`Vec`], this will be the number of elements).
//!
//! * All integers and floating point numbers are encoded in little-endian format (due to both
//!   its prevalence in normal hardware and it being the numeric format WASM uses).
//!
//! These rules are not mandatory, but it is strongly recommended to follow them.
//!
//! ## Remarks
//!
//! All integer types are guaranteed to have a constant size equal to `std::mem::size_of<T>()`.

use arrayvec::ArrayVec;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use unicard_types_macro::WasmType32 as WasmType;

/// An error occurred whilst allocating, reading from, or writing to WASM32 memory.
///
/// The primary reason for this error is due to a lack of memory (e.g., `read_u64` was
/// called, but there are fewer than 8 bytes of memory left to read), although it may
/// returned for other reasons (e.g., if WASM's memory contains an invalid value).
///
/// # Remarks
///
/// These `32` types are meant only for wasm32 instances (instances with 32-bit pointers), and will
/// make assumptions on that premise (e.g., that any type >`4GiB` will not fit into wasm memory).
#[derive(Debug)]
#[non_exhaustive]
pub struct WasmMemoryError32 {
    kind: WasmMemoryErrorKind,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[non_exhaustive]
enum WasmMemoryErrorKind {
    /// An allocation is too large to reasonably fulfil.
    AllocationTooLarge,

    /// A read/write attempted to go beyond the boundaries of the allocation/WASM32 memory.
    ///
    /// For example, if you try to read a `u32` on the last byte of WASM memory.
    MemoryOverflow,

    /// The value being read from WASM memory is invalid for the type.
    ///
    /// For example, if you are reading an enum with three variants and the first
    /// `u32` (the discriminant) has a value of `367`, which exceeds the highest
    /// discriminant value for the enum (`2`).
    InvalidValue,
}

impl WasmMemoryError32 {
    /// An allocation request for WASM32 memory was too large to fulfil.
    #[inline]
    pub fn alloc_too_large() -> Self {
        Self {
            kind: WasmMemoryErrorKind::AllocationTooLarge,
        }
    }

    /// A read/write surpassed the boundaries of its allocation/the WASM32 memory.
    ///
    /// For example, if you are reading a `u32` from the last byte of WASM32
    /// memory.
    ///
    /// # Remarks
    ///
    /// This does not necessarily refer to WASM32 memory -- for instance, a [`WasmReader32`] may
    /// be reading from an allocation which is not large enough to fulfil a read request.
    #[inline]
    pub fn memory_overflow() -> Self {
        Self {
            kind: WasmMemoryErrorKind::MemoryOverflow,
        }
    }

    /// The WASM32 memory contains an invalid value of the type you are reading.
    ///
    /// For example, a discriminator of `342` being read for an enum which only
    /// has three variants.
    #[inline]
    pub fn invalid_value() -> Self {
        Self {
            kind: WasmMemoryErrorKind::InvalidValue,
        }
    }
}

impl Display for WasmMemoryError32 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use WasmMemoryErrorKind as Kind;

        match self.kind {
            Kind::AllocationTooLarge => {
                f.write_str("there is insufficient WASM32 memory to fulfil the alloc request")
            }
            Kind::MemoryOverflow => {
                f.write_str("there is insufficient WASM32 memory to perform this action")
            }
            Kind::InvalidValue => f.write_str("WASM32 memory contains an invalid value"),
        }
    }
}

impl std::error::Error for WasmMemoryError32 {}

/// A reader capable of reading directly from WASM32 memory, or an allocation in WASM32 memory.
///
/// # Remarks
///
/// These `32` types are only meant for wasm32 instances (WASM instances with 32-bit pointers), and
/// will make further assumptions on this premise (e.g., that a type >`4GiB` will not fit into
/// WASM memory).
pub trait WasmReader32 {
    /// Read enough bytes from WASM32 memory to fill `bytes`.
    ///
    /// # Returns
    ///
    /// [`Ok(())`](Ok) if `bytes.len()` bytes were successfully read from (and copied
    /// to `bytes`) WASM32 memory, [`Err(WasmMemoryError32)`](WasmMemoryError32) otherwise.
    ///
    /// # Remarks
    ///
    /// Failures of this function should be considered "fatal" (i.e., the WASM32 instance becomes
    /// "poisoned" and should be discarded).
    ///
    /// This function may write to `bytes`, even if it fails -- the reason for this behaviour
    /// is due to the fact failures should be considered "fatal" (see above), and because of the
    /// difficulty in determining whether a read will be successful.
    fn read(&mut self, bytes: &mut [u8]) -> Result<(), WasmMemoryError32>;
}

/// A writer capable of writing directly to WASM32 memory, or an allocation in WASM32 memory.
///
/// # Remarks
///
/// These `32` types are intended only for wasm32 instances (that is, wasm instances with 32-bit
/// wide pointers), and will make further assumptions on this premise (e.g., that a type >`4GiB`
/// will not fit into wasm memory).
pub trait WasmWriter32 {
    /// Write `bytes` to WASM32 memory.
    ///
    /// # Returns
    ///
    /// [`Ok(())`](Ok) if **all** bytes were successfully written,
    /// [`Err(WasmMemoryError32)`](WasmMemoryError32) otherwise (e.g., if there was not enough
    /// memory available to write the entirety of `bytes`).
    ///
    /// # Remarks
    ///
    /// Failures of this function should be considered "fatal" (i.e., the WASM32 instance becomes
    /// "poisoned" and should be discarded).
    ///
    /// This function may write to WASM32 memory, even if it fails -- the reason for this behaviour
    /// is due to the fact failures should be considered "fatal" (see above), and because of the
    /// difficulty in determining whether a write will fail.
    fn write(&mut self, bytes: &[u8]) -> Result<(), WasmMemoryError32>;
}

/// A WASM32 memory allocator.
pub trait WasmAllocator32 {
    /// The writer type used to write to an allocation.
    type Writer: WasmWriter32;

    /// Allocate a chunk of WASM32 memory **at least** `size` bytes in length.
    ///
    /// # Returns
    ///
    /// A writer to the new allocation if successful, an error if unsuccessful.
    ///
    /// # Remarks
    ///
    /// The `writer` may fail to write bytes beyond the requested allocation boundary, even if
    /// there is sufficient WASM32 memory to fulfil the request or the allocation's true size
    /// is larger than the request size.
    fn alloc(&mut self, size: u32) -> Result<Self::Writer, WasmMemoryError32>;
}

/// A type which can be read from/written to WASM32 memory.
///
/// # Remarks
///
/// These `32` types are intended only for wasm32 instances (that is wasm instances with 32-bit
/// wide pointers), and will make further assumptions based on this premise (e.g., that a type
/// >`4GiB` will not fit into WASM memory).
pub trait WasmType32: Sized {
    /// Read a value of the type from WASM32 memory.
    ///
    /// # Remarks
    ///
    /// [`reader.read`](WasmReader32::read) may be called, even if `Err` is
    /// returned.
    ///
    /// Failures of this function should be considered "fatal", meaning the WASM32
    /// instance should be ejected immediately. The reason for this behaviour is
    /// due to the inability to reasonably recover from a [`WasmReader32::read`] error
    /// (i.e., if we can't read a critical type from memory, there's not much
    /// point in continuing).
    ///
    /// See [`WasmReader32::read`] for more information.
    fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32>;

    /// The size of the encoded type, in bytes.
    ///
    /// # Returns
    ///
    /// [`Some`] if the size of the type is able to fit into a `u32`, [`None`] otherwise.
    fn size(&self) -> Option<u32>;

    /// Write a value of the type to WASM32 memory.
    ///
    /// # Remarks
    ///
    /// [`writer.write`](WasmWriter32::write) may be called, even if `Err` is returned.
    ///
    /// Failures of this function should be considered "fatal", meaning the WASM
    /// instance should be ejected immediately. The reason for this behaviour is
    /// due to the inability to reasonably recover from a [`WasmWriter32::write`] error
    /// (i.e., if we can't write a critical type into memory, there's not much
    /// point in continuing).
    ///
    /// This function is not expected to run any size checks prior to writing (even rudimentary
    /// ones, like ensuring [`self.size`](WasmType32::size) returns [`Some`]) -- there are
    /// two reasons for this behaviour:
    ///
    /// * The caller is expected to call [`self.size`](WasmType32::size) (in order to
    ///    determine how much memory to allocate for the writer).
    ///
    /// * The writer should ensure no bytes are written beyond the allocation anyway.
    ///
    /// See [`WasmWriter32::write`] for more information.
    fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32>;

    /// Allocate enough memory for the type's WASM32 representation and write to that allocation.
    ///
    /// This method is primarily a convenience function which ensures that `self.size` is
    /// properly checked and used to allocate the correct amount of WASM32 memory. This ensures
    /// there are no mix-ups: for example, if the wrong `size` is used to create the allocation
    /// which, in turn, causes a memory overflow error to be returned when writing, which
    /// generally indicates a buggy `WasmType32` implementation rather than an allocation issue.
    #[inline]
    fn alloc(&self, allocator: &mut impl WasmAllocator32) -> Result<(), WasmMemoryError32> {
        // NOTE: if `size` exceeds `u32::MAX` (and hence `self.size()` returns `None`), `alloc`
        //       is guaranteed to fail.
        let Some(size) = self.size() else {
            return Err(WasmMemoryError32::alloc_too_large());
        };

        // Retrieve a writer
        let mut writer = allocator.alloc(size)?;
        self.write(&mut writer)
    }
}

// Derive `WasmType` for numeric types
macro_rules! derive_type_methods {
    ($ty:ty) => {
        impl WasmType32 for $ty {
            #[inline]
            fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
                let mut bytes = [0u8; std::mem::size_of::<$ty>()];
                reader.read(&mut bytes)?;
                Ok(<$ty>::from_le_bytes(bytes))
            }

            #[inline]
            fn size(&self) -> Option<u32> {
                u32::try_from(std::mem::size_of::<$ty>()).ok()
            }

            #[inline]
            fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
                // Debug assertion for debugging purposes
                debug_assert!(self.size().is_some());

                writer.write(&self.to_le_bytes())?;
                Ok(())
            }
        }
    };
}

derive_type_methods!(u8);
derive_type_methods!(u16);
derive_type_methods!(u32);
derive_type_methods!(u64);

derive_type_methods!(i8);
derive_type_methods!(i16);
derive_type_methods!(i32);
derive_type_methods!(i64);

impl<T, const N: usize> WasmType32 for [T; N]
where
    T: WasmType32,
{
    #[inline]
    fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
        // NOTE: `ArrayVec` is used for two reasons:
        //   1. It is impossible to create an uninitialised array in Rust without
        //      the use of MaybeUninit, which requires unsafe code
        //
        //   2. The use of MaybeUninit results in memory leaks if a panic occurs
        //      -- `ArrayVec` solves this issue
        let mut stack_vec = ArrayVec::<T, N>::new();

        // NOTE: we do not push the size as it is known at compile time (it'd be like
        //       including the size, in bytes, of a `u32` before reading it)

        for _ in 0..N {
            stack_vec.push(T::read(reader)?);
        }

        match stack_vec.into_inner() {
            Ok(array) => Ok(array),
            Err(_) => unreachable!("stack_vec should be initialised with N elements"),
        }
    }

    #[inline]
    fn size(&self) -> Option<u32> {
        self.iter()
            .try_fold(0u32, |acc, el| acc.checked_add(el.size()?))
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
        debug_assert!(self.size().is_some());

        for element in self {
            element.write(writer)?;
        }

        Ok(())
    }
}

// NOTE: an implementation cannot be offered for slices as it is impossible to read a slice
// (slices are references, and returning a reference to a stack-allocated object is a no-no
// in any language).
impl<T> WasmType32 for Vec<T>
where
    T: WasmType32,
{
    #[inline]
    fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
        // The number of items in the list
        let len = u32::read(reader)?;
        let mut items = Vec::with_capacity(len as usize);

        for _ in 0..len {
            items.push(T::read(reader)?);
        }

        Ok(items)
    }

    #[inline]
    fn size(&self) -> Option<u32> {
        // NOTE: a `Vec<T>` is capable of holding ZSTs -- as a result, we have to check
        // that the length of the vector does not exceed `u32::MAX`: the reason for this
        // is because the length of the vector is encoded as a `u32`, meaning any length
        // larger than a `u32` will overflow and cause issues.
        if self.len() as u64 > u32::MAX as u64 {
            return None;
        }

        // NOTE: we cannot do self.len() * self[0].size(), as it assumes size is constant across
        // all types (a prime example of a dynamically-sized type is the type we're implementing
        // right now!)
        // NOTE: the `4` is required as the number of elements is encoded as a `u32` at
        //       the start.
        self.iter()
            .try_fold(4u32, |acc, el| acc.checked_add(el.size()?))
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
        debug_assert!(self.size().is_some());

        // We have to do the same check here as a protection -- if a `None` return of `size()` is
        // ignored, the `write` method should still fail, just with a less intuitive error
        // message
        if self.len() as u64 > u32::MAX as u64 {
            return Err(WasmMemoryError32::memory_overflow());
        }

        // Write length
        u32::write(&(self.len() as u32), writer)?;

        // Write elements
        for el in self {
            el.write(writer)?;
        }

        Ok(())
    }
}

impl WasmType32 for String {
    #[inline]
    fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
        // Read the length of the string
        let length = u32::read(reader)?;

        // Read `length` bytes from WASM memory
        let mut bytes = vec![0; length as usize];
        reader.read(&mut bytes)?;

        // Convert the bytes from UTF-8
        // NOTE: if the bytes are not UTF-8, it is considered a problem of
        // the WASM module (i.e., the WASM module is responsible for enforcing
        // the validity of UTF-8 strings).
        String::from_utf8(bytes).map_err(|_| WasmMemoryError32::invalid_value())
    }

    #[inline]
    fn size(&self) -> Option<u32> {
        // NOTE: we do not need to do a `len` check here as a string is effectively a vec
        // of bytes representing UTF-8 code units -- as a byte (`u8`) is not a ZST, we do not
        // need to check `len`: if `len() > u32::MAX`, then the following calculation should
        // fail regardless

        u32::try_from(self.len()).ok()?.checked_add(4)
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
        (self.len() as u32).write(writer)?;

        // NOTE: the bytes came from a `String`, which guarantees that the bytes
        // are valid UTF-8 (as a string can only hold valid UTF-8).
        writer.write(self.as_bytes())?;

        Ok(())
    }
}

macro_rules! derive_tuple {
    ( $($generic:ident),+ ) => {
        // NOTE: the comma is included as part of the expansion (rather than
        // as the separator) to avoid ambiguity (i.e., `(T,)` is a tuple, `(T)` is
        // treated as `T`.
        #[automatically_derived]
        #[allow(clippy::needless_question_mark)]
        impl<$($generic),+> WasmType32 for ($($generic,)+)
        where
            $( $generic: WasmType32 ),+
        {
            fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
                Ok((
                    $( <$generic as WasmType32>::read(&mut *reader)?, )+
                ))
            }

            fn size(&self) -> Option<u32> {
                #[allow(non_snake_case)]
                let ($(ref $generic,)+) = self;
                Some(0u32
                $( .checked_add($generic.size()?)? )+)
            }

            fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
                debug_assert!(self.size().is_some());

                #[allow(non_snake_case)]
                let ($(ref $generic,)+) = self;

                // For a similar reason as explained for fixed size arrays,
                // we do not write the number of elements first, as this should
                // be known at compile time
                $($generic.write(&mut *writer)?;)+
                Ok(())
            }
        }
    };
}

impl WasmType32 for () {
    #[inline]
    fn read(_reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
        Ok(())
    }

    #[inline]
    fn size(&self) -> Option<u32> {
        Some(0)
    }

    #[inline]
    fn write(&self, _writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
        Ok(())
    }
}

derive_tuple!(A);
derive_tuple!(A, B);
derive_tuple!(A, B, C);
derive_tuple!(A, B, C, D);
derive_tuple!(A, B, C, D, E);
derive_tuple!(A, B, C, D, E, F);
derive_tuple!(A, B, C, D, E, F, G);
derive_tuple!(A, B, C, D, E, F, G, H);
derive_tuple!(A, B, C, D, E, F, G, H, I);
derive_tuple!(A, B, C, D, E, F, G, H, I, J);
derive_tuple!(A, B, C, D, E, F, G, H, I, J, K);
derive_tuple!(A, B, C, D, E, F, G, H, I, J, K, L);

impl<K, V> WasmType32 for HashMap<K, V>
where
    K: Eq + Hash + WasmType32,
    V: WasmType32,
{
    fn read(reader: &mut impl WasmReader32) -> Result<Self, WasmMemoryError32> {
        // Retrieve the number of elements in the map
        let size = u32::read(reader)?;
        let mut hash_map = Self::with_capacity(size as usize);

        for _ in 0..size {
            let key = K::read(reader)?;
            let value = V::read(reader)?;
            if hash_map.insert(key, value).is_some() {
                // `HashMap` must have unique keys (i.e., one value per key) -- if wasm
                // memory had duplicate keys, it has violated this condition, and is therefore
                // an invalid value
                return Err(WasmMemoryError32::invalid_value());
            }
        }

        Ok(hash_map)
    }

    fn size(&self) -> Option<u32> {
        // NOTE: this is required in the event `HashMap::len()` exceeds `u32::MAX`: as we
        // encode the number of elements as a `u32`, any HashMap with more than `u32::MAX` elements
        // is unencodable, and should be rejected. This only applies to HashMaps where both
        // the key and the value are ZSTs
        // NOTE 2: whilst it should be impossible for such a situation in which there are any more
        // than one entry in a HashMap with a zero-sized key (as all zero-sized types which
        // implement `Eq` should have all values compare equal to each other), this check is
        // kept as an additional precaution
        if self.len() as u64 >= u32::MAX as u64 {
            return None;
        }

        self.iter().try_fold(4u32, |acc, (k, v)| {
            let acc = acc.checked_add(k.size()?)?;
            acc.checked_add(v.size()?)
        })
    }

    fn write(&self, writer: &mut impl WasmWriter32) -> Result<(), WasmMemoryError32> {
        debug_assert!(self.size().is_some());

        if self.len() as u64 > u32::MAX as u64 {
            return Err(WasmMemoryError32::memory_overflow());
        }

        // Write the number of elements
        u32::write(&(self.len() as u32), writer)?;

        // Write the values
        for (k, v) in self {
            k.write(writer)?;
            v.write(writer)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A mock WASM reader/allocator/writer.
    struct Mock {
        cursor: usize,
        memory: Vec<u8>,
    }

    impl Mock {
        fn new() -> Self {
            Mock {
                cursor: 0,
                memory: Vec::new(),
            }
        }

        fn with(bytes: &[u8]) -> Self {
            Mock {
                cursor: 0,
                memory: bytes.to_owned(),
            }
        }
    }

    impl WasmReader32 for Mock {
        fn read(&mut self, bytes: &mut [u8]) -> Result<(), WasmMemoryError32> {
            if self.memory.len() < (self.cursor + bytes.len()) {
                return Err(WasmMemoryError32::memory_overflow());
            }

            bytes.copy_from_slice(&self.memory[self.cursor..(self.cursor + bytes.len())]);
            self.cursor += bytes.len();

            Ok(())
        }
    }

    impl WasmWriter32 for Mock {
        fn write(&mut self, bytes: &[u8]) -> Result<(), WasmMemoryError32> {
            self.memory.extend_from_slice(bytes);
            Ok(())
        }
    }

    #[test]
    fn wasm_read_vec() {
        let mut mock = Mock::with(&[2, 0, 0, 0, 1, 0, 0, 0, 65, 2, 0, 0, 0, 97, 98]);
        let vec = Vec::<String>::read(&mut mock).expect("for read to be successful");

        assert_eq!(&vec[0], "A");
        assert_eq!(&vec[1], "ab");
    }

    #[test]
    fn wasm_write_vec() {
        let mut mock = Mock::new();
        let vec = vec![(10, 8u8), (15, 0)];

        assert_eq!(vec.size(), Some(14));

        vec.write(&mut mock).expect("write to be successful");

        assert_eq!(&mock.memory, &[2, 0, 0, 0, 10, 0, 0, 0, 8, 15, 0, 0, 0, 0]);
    }

    #[test]
    fn wasm_read_string() {
        let mut mock = Mock::with(&[8, 0, 0, 0, b'b', b'a', b'c', b'k', b' ', b'f', b'o', b'x']);
        let string = String::read(&mut mock).expect("read to be successful");

        assert_eq!(&string, "back fox");
    }

    #[test]
    fn wasm_write_string() {
        let mut mock = Mock::new();
        let string = "Back!".to_string();

        assert_eq!(string.size(), Some(9));

        string.write(&mut mock).expect("write to be successful");
        assert_eq!(&mock.memory, &[5, 0, 0, 0, b'B', b'a', b'c', b'k', b'!']);
    }

    #[test]
    fn wasm_read_array() {
        let mut mock = Mock::with(&[6, 7, 8, 9]);
        let array = <[u8; 4] as WasmType32>::read(&mut mock).expect("read to be successful");

        assert_eq!(array, [6, 7, 8, 9]);
    }

    #[test]
    fn wasm_write_array() {
        let mut mock = Mock::new();
        let array = [0, 1, 2];

        assert_eq!(array.size(), Some(12));

        array.write(&mut mock).expect("write to be successful");
        assert_eq!(&mock.memory, &[0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]);
    }

    #[test]
    fn wasm_read_tuple() {
        let mut mock = Mock::with(&[254, 255, 255, 255, 1, 0, 0, 0, b'=', 1, 0, 0, 0, 0]);
        let tuple =
            <(i32, String, Vec<u8>) as WasmType32>::read(&mut mock).expect("read to be successful");

        assert_eq!(tuple.0, -2);
        assert_eq!(&tuple.1, "=");
        assert_eq!(&tuple.2, &[0]);
    }

    #[test]
    fn wasm_write_tuple() {
        let mut mock = Mock::new();
        let tuple = ([69u8; 3], 1, 2, 3);

        assert_eq!(tuple.size(), Some(15));

        tuple.write(&mut mock).expect("write to be successful");
        assert_eq!(
            &mock.memory,
            &[69, 69, 69, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]
        );
    }

    #[test]
    fn wasm_read_hash_map() {
        let mut mock = Mock::with(&[2, 0, 0, 0, 1, 0, 0, 0, b'6', 6, 1, 0, 0, 0, b'9', 9]);
        let map =
            <HashMap<String, u8> as WasmType32>::read(&mut mock).expect("read to be successful");

        assert_eq!(map.get("6").unwrap(), &6);
        assert_eq!(map.get("9").unwrap(), &9);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn wasm_write_hash_map() {
        let mut mock = Mock::new();
        let mut map = HashMap::new();
        let _ = map.insert(18, (1u8, 2u8));
        let _ = map.insert(29, (6u8, 1u8));

        assert_eq!(map.size(), Some(4 + 8 + 4));
        map.write(&mut mock).expect("write to be successful");

        // NOTE: the default hasher for HashMap uses a randomly generated seed to
        // mitigate DoS attacks (e.g., where the attacker attempts to generate multiple
        // entries whose keys have the same hash, resulting in poor HashMap performance).
        // As a result, `iter` (which returns values in _hash_ order, not insertion
        // order) will return the elements randomly, making it difficult to assert.
        // To avoid this, we run iter ourselves to get an understanding of the order
        // and hence the assertion we must perform.
        if *map.iter().next().unwrap().0 == 18 {
            assert_eq!(
                &mock.memory,
                &[
                    2, 0, 0, 0, // KEY 1
                    18, 0, 0, 0, // VALUE 1
                    1, 2, // KEY 2
                    29, 0, 0, 0, // VALUE 2
                    6, 1
                ]
            );
        } else {
            assert_eq!(
                &mock.memory,
                &[
                    2, 0, 0, 0, // KEY 1
                    29, 0, 0, 0, // VALUE 1
                    6, 1, // KEY 2
                    18, 0, 0, 0, // VALUE 2
                    1, 2
                ]
            );
        }
    }

    #[test]
    fn read_zst_vec() {
        // Ideally, we would test a vec with `u32::MAX` elements however, due to
        // tests being ran in debug mode, it takes too much time to read such a
        // vector (as it effectively has to call vec.push u32::MAX times)
        let mut mock = Mock::with(&[255, 0, 0, 0]);
        let vec = Vec::<()>::read(&mut mock).expect("read to succeed");

        assert_eq!(vec.len(), 255);
    }

    #[test]
    fn write_zst_vec() {
        let vec = vec![(); 256];
        let mut mock = Mock::new();

        assert_eq!(vec.size(), Some(4));

        vec.write(&mut mock).expect("write to be successful");

        assert_eq!(&mock.memory, &[0, 1, 0, 0]);
    }

    #[test]
    fn write_zst_vec_too_large() {
        let mut vec = Vec::<()>::new();
        vec.reserve(u32::MAX as usize + 1);
        // Probably safe -- reading ZSTs should be a no-op, including
        // for ptr::read (meaning ptr::read for an invalid, albeit non-null
        // and properly aligned, address is completely safe for a ZST).
        unsafe {
            vec.set_len(vec.capacity());
        }

        assert_eq!(vec.size(), None);
    }
}
