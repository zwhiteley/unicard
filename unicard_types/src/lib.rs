use std::fmt::{Display, Formatter};
use arrayvec::ArrayVec;

/// An error occurred whilst allocating, reading from, or writing to WASM memory.
///
/// The primary reason for this error is due to a lack of memory (e.g., `read_u64` was
/// called, but there are fewer than 8 bytes of memory left to read), although it may
/// returned for other reasons (e.g., if WASM's memory contains an invalid value).
#[derive(Debug)]
#[non_exhaustive]
pub struct WasmMemoryError {
    kind: WasmMemoryErrorKind
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[non_exhaustive]
enum WasmMemoryErrorKind {
    /// There was insufficient memory to complete the operation.
    ///
    /// For example, if you try to read a `u32` on the last byte of WASM memory.
    ///
    /// # Remarks
    ///
    /// This does not necessarily refer to WASM memory (e.g., if the [`WasmReader`] is reading
    /// from an allocation, and the allocation does not have enough memory to fulfil the request).
    InsufficientMemory,

    /// The value being read from WASM memory is invalid for the type.
    ///
    /// For example, if you are reading an enum with three variants and the first
    /// `u32` (the discriminant) has a value of `367`, which exceeds the highest
    /// discriminant value for the enum (`2`).
    InvalidValue
}


impl WasmMemoryError {
    /// There was insufficient memory left to complete the operation.
    ///
    /// For example, if you are reading a `u32` from the last byte of WASM
    /// memory.
    ///
    /// # Remarks
    ///
    /// This does not necessarily refer to WASM memory -- for instance, a [`WasmReader`] may
    /// be reading from an allocation which is not large enough to fulfil a read request.
    #[inline]
    pub fn out_of_memory() -> Self {
        Self {
            kind: WasmMemoryErrorKind::InsufficientMemory
        }
    }

    /// The WASM memory contains an invalid value of the type you are reading.
    ///
    /// For example, a discriminator of `342` being read for an enum which only
    /// has three variants.
    #[inline]
    pub fn invalid_value() -> Self {
        Self {
            kind: WasmMemoryErrorKind::InvalidValue
        }
    }
}

impl Display for WasmMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use WasmMemoryErrorKind as Kind;

        match self.kind {
            Kind::InsufficientMemory => f.write_str("there is insufficient WASM memory to perform this action"),
            Kind::InvalidValue => f.write_str("WASM memory contains an invalid value")
        }
    }
}

impl std::error::Error for WasmMemoryError {}

/// A reader capable of reading directly from WASM memory, or an allocation in WASM memory.
pub trait WasmReader {
    /// Read enough bytes from WASM memory to fill `bytes`.
    ///
    /// # Returns
    ///
    /// [`Ok(())`](Ok) if `bytes.len()` bytes were successfully read from (and copied
    /// to `bytes`) WASM memory, [`Err(WasmMemoryError)`](WasmMemoryError) otherwise.
    ///
    /// # Remarks
    ///
    /// Failures of this function should be considered "fatal" (i.e., the WASM instance becomes
    /// "poisoned" and should be discarded).
    ///
    /// This function may write to `bytes`, even if it fails -- the reason for this behaviour
    /// is due to the fact failures should be considered "fatal" (see above).
    fn read(&mut self, bytes: &mut [u8]) -> Result<(), WasmMemoryError>;
}

/// A writer capable of writing directly to WASM memory, or an allocation in WASM memory.
pub trait WasmWriter {
    /// Write `bytes` to WASM memory.
    ///
    /// # Returns
    ///
    /// [`Ok(())`](Ok) if **all** bytes were successfully written,
    /// [`Err(WasmMemoryError)`](WasmMemoryError) otherwise (e.g., if there was not enough
    /// memory available to write the entirety of `bytes`).
    ///
    /// # Remarks
    ///
    /// Failures of this function should be considered "fatal" (i.e., the WASM instance becomes
    /// "poisoned" and should be discarded).
    ///
    /// This function may write to WASM memory, even if it fails -- the reason for this behaviour
    /// is due to the fact failures should be considered "fatal" (see above).
    fn write(&mut self, bytes: &[u8]) -> Result<(), WasmMemoryError>;
}

/// A type which can be read from/written to WASM memory.
pub trait WasmType: Sized {
    /// Read a value of the type from WASM memory.
    ///
    /// # Remarks
    ///
    /// [`reader.read`](WasmReader::read) may be called, even if `Err` is
    /// returned.
    ///
    /// Failures of this function should be considered "fatal", meaning the WASM
    /// instance should be ejected immediately. The reason for this behaviour is
    /// due to the inability to reasonably recover from a [`WasmReader::read`] error
    /// (i.e., if we can't read a critical type from memory, there's not much
    /// point in continuing).
    ///
    /// See [`WasmReader::read`] for more information.
    fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError>;

    /// The size of the encoded type, in bytes.
    fn size(&self) -> usize;

    /// Write a value of the type to WASM memory.
    ///
    /// # Remarks
    ///
    /// [`writer.write`](WasmWriter::write) may be called, even if `Err` is returned.
    ///
    /// Failures of this function should be considered "fatal", meaning the WASM
    /// instance should be ejected immediately. The reason for this behaviour is
    /// due to the inability to reasonably recover from a [`WasmWriter::write`] error
    /// (i.e., if we can't write a critical type into memory, there's not much
    /// point in continuing).
    ///
    /// See [`WasmWriter::write`] for more information.
    fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError>;
}

// Derive `WasmType` for numeric types
macro_rules! derive_type_methods {
    ($ty:ty) =>  {
        impl WasmType for $ty {
            #[inline]
            fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError> {
                let mut bytes = [0u8; std::mem::size_of::<$ty>()];
                reader.read(&mut bytes)?;
                Ok(<$ty>::from_le_bytes(bytes))
            }

            #[inline]
            fn size(&self) -> usize {
                std::mem::size_of::<$ty>()
            }

            #[inline]
            fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError> {
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

impl<T, const N: usize> WasmType for [T; N]
where
    T: WasmType
{
    #[inline]
    fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError> {
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
            Err(_) => unreachable!("stack_vec should be initialised with N elements")
        }
    }

    #[inline]
    fn size(&self) -> usize {
        self.iter().fold(0, |acc, el| acc + el.size())
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError> {
        for element in self {
            element.write(writer)?;
        }

        Ok(())
    }
}

// NOTE: an implementation cannot be offered for slices as it is impossible to read a slice
// (slices are references, and returning a reference to a stack-allocated object is a no-no
// in any language).
impl<T> WasmType for Vec<T>
    where T: WasmType
{
    #[inline]
    fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError> {
        // The number of items in the list
        let len = u32::read(reader)?;
        let mut items = Vec::with_capacity(len as usize);

        for _ in 0..len {
            items.push(T::read(reader)?);
        }

        Ok(items)
    }

    #[inline]
    fn size(&self) -> usize {
        // NOTE: we cannot do self.len() * self[0].size(), as it assumes size is constant across
        // all types (a prime example of a dynamically-sized type is the type we're implementing
        // right now!)
        // NOTE: `+ 4` is required as a `u32` length is prepended to the output
        self.iter().fold(0, |acc, item| acc + item.size()) + 4
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError> {
        if self.len() as u32 > u32::MAX {
            // pointers in WASM are 32 bits, meaning any vector with a length higher is
            // impossible.
            //
            // According to the spec, the "limits" of memory must be in the range 2^16 ("limits"
            // referring to the min/max size of the memory, in pages). A page is 2^16 bytes.
            // Therefore, the maximum size of WASM32 memory is <2^16 * 2^16 = 2^32, or u32::MAX
            // bytes.
            return Err(WasmMemoryError::out_of_memory());
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

impl WasmType for String {
    #[inline]
    fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError> {
        // Read the length of the string
        let length = u32::read(reader)?;

        // Read `length` bytes from WASM memory
        let mut bytes = vec![0; length as usize];
        reader.read(&mut bytes)?;

        // Convert the bytes from UTF-8
        // NOTE: if the bytes are not UTF-8, it is considered a problem of
        // the WASM module (i.e., the WASM module is responsible for enforcing
        // the validity of UTF-8 strings).
        String::from_utf8(bytes)
            .map_err(|_| WasmMemoryError::invalid_value())
    }

    #[inline]
    fn size(&self) -> usize {
        assert!(self.len() <= u32::MAX as usize);
        self.len() + (self.len() as u32).size()
    }

    #[inline]
    fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError> {
        assert!(self.len() <= u32::MAX as usize);

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
        impl<$($generic),+> WasmType for ($($generic,)+)
        where
            $( $generic: WasmType ),+
        {
            fn read(reader: &mut impl WasmReader) -> Result<Self, WasmMemoryError> {
                Ok((
                    $( <$generic as WasmType>::read(&mut *reader)?, )+
                ))
            }

            fn size(&self) -> usize {
                #[allow(non_snake_case)]
                let ($(ref $generic,)+) = self;
                $($generic.size() + )+ 0
            }

            fn write(&self, writer: &mut impl WasmWriter) -> Result<(), WasmMemoryError> {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A mock WASM reader/allocator/writer.
    struct Mock {
        cursor: usize,
        memory: Vec<u8>
    }

    impl Mock {
        fn new() -> Self {
            Mock {
                cursor: 0,
                memory: Vec::new()
            }
        }

        fn with(bytes: &[u8]) -> Self {
            Mock {
                cursor: 0,
                memory: bytes.to_owned()
            }
        }
    }

    impl WasmReader for Mock {
        fn read(&mut self, bytes: &mut [u8]) -> Result<(), WasmMemoryError> {
            if self.memory.len() < (self.cursor + bytes.len()) {
                return Err(WasmMemoryError::out_of_memory());
            }

            bytes.copy_from_slice(&self.memory[self.cursor..(self.cursor + bytes.len())]);
            self.cursor += bytes.len();

            Ok(())
        }
    }

    impl WasmWriter for Mock {
        fn write(&mut self, bytes: &[u8]) -> Result<(), WasmMemoryError> {
            self.memory.extend_from_slice(bytes);
            Ok(())
        }
    }
    #[test]
    fn wasm_read_vec() {
        let mut mock = Mock::with(&[2, 0, 0, 0, 1, 0, 0, 0, 65, 2, 0, 0, 0, 97, 98]);
        let vec = Vec::<String>::read(&mut mock)
            .expect("for read to be successful");

        assert_eq!(&vec[0], "A");
        assert_eq!(&vec[1], "ab");
    }

    #[test]
    fn wasm_write_vec() {
        let mut mock = Mock::new();
        let vec = vec![(10, 8u8), (15, 0)];

        assert_eq!(vec.size(), 14);

        vec.write(&mut mock).expect("write to be successful");

        assert_eq!(&mock.memory, &[
            2, 0, 0, 0,
            10, 0, 0, 0, 8,
            15, 0, 0, 0, 0
        ]);
    }

    #[test]
    fn wasm_read_string() {
        let mut mock = Mock::with(&[
            8, 0, 0, 0,
            b'b', b'a', b'c', b'k',
            b' ', b'f', b'o', b'x'
        ]);
        let string = String::read(&mut mock)
            .expect("read to be successful");

        assert_eq!(&string, "back fox");
    }

    #[test]
    fn wasm_write_string() {
        let mut mock = Mock::new();
        let string = "Back!".to_string();

        assert_eq!(string.size(), 9);

        string.write(&mut mock).expect("write to be successful");
        assert_eq!(&mock.memory, &[
            5, 0, 0, 0,
            b'B', b'a', b'c', b'k', b'!'
        ]);
    }

    #[test]
    fn wasm_read_array() {
        let mut mock = Mock::with(&[
            6, 7, 8, 9
        ]);
        let array = <[u8; 4] as WasmType>::read(&mut mock)
            .expect("read to be successful");

        assert_eq!(array, [6, 7, 8, 9]);
    }

    #[test]
    fn wasm_write_array() {
        let mut mock = Mock::new();
        let array = [0, 1, 2];

        assert_eq!(array.size(), 12);

        array.write(&mut mock).expect("write to be successful");
        assert_eq!(&mock.memory, &[
            0, 0, 0, 0,
            1, 0, 0, 0,
            2, 0, 0, 0
        ]);
    }

    #[test]
    fn wasm_read_tuple() {
        let mut mock = Mock::with(&[
            254, 255, 255, 255,
            1, 0, 0, 0, b'=',
            1, 0, 0, 0, 0
        ]);
        let tuple = <(i32, String, Vec<u8>) as WasmType>::read(&mut mock)
            .expect("read to be successful");

        assert_eq!(tuple.0, -2);
        assert_eq!(&tuple.1, "=");
        assert_eq!(&tuple.2, &[0]);
    }

    #[test]
    fn wasm_write_tuple() {
        let mut mock = Mock::new();
        let tuple = ([69u8; 3], 1, 2, 3);

        assert_eq!(tuple.size(), 15);

        tuple.write(&mut mock).expect("write to be successful");
        assert_eq!(&mock.memory, &[
            69, 69, 69,
            1, 0, 0, 0,
            2, 0, 0, 0,
            3, 0, 0, 0
        ]);
    }
}