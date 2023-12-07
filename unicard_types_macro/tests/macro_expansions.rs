pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

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
    fn read(&mut self, bytes: &mut [u8]) -> Result<(), unicard_types::WasmMemoryError32> {
        if self.memory.len() < (self.cursor + bytes.len()) {
            return Err(unicard_types::WasmMemoryError32::memory_overflow());
        }

        bytes.copy_from_slice(&self.memory[self.cursor..(self.cursor + bytes.len())]);
        self.cursor += bytes.len();

        Ok(())
    }
}

impl WasmWriter32 for Mock {
    fn write(&mut self, bytes: &[u8]) -> Result<(), unicard_types::WasmMemoryError32> {
        self.memory.extend_from_slice(bytes);
        Ok(())
    }
}

#[derive(WasmType)]
struct Unit;

#[test]
fn unit_read() {
    let mut reader = Mock::new();
    let _ = Unit::read(&mut reader).expect("valid unit type");
}

#[test]
fn unit_write() {
    let mut allocator = Mock::new();
    let unit = Unit;

    unit.write(&mut allocator).expect("write to be successful");
}

#[derive(Debug, WasmType, PartialEq)]
struct Tuple(i32, i32, i32);

#[test]
fn tuple_read() {
    let mut reader = Mock::with(&[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0]);
    let tuple = Tuple::read(&mut reader).expect("valid unit type");

    assert_eq!(tuple.0, 10);
    assert_eq!(tuple.1, 20);
    assert_eq!(tuple.2, 30);
}

#[test]
fn tuple_write() {
    let mut writer = Mock::new();
    let tuple = Tuple(69, 69, -1);

    tuple.write(&mut writer).expect("write to be successful");

    assert_eq!(tuple.size(), Some(writer.memory.len() as u32));

    let tuple_read = Tuple::read(&mut writer).expect("read to be valid");
    assert_eq!(tuple, tuple_read);
}

#[derive(Debug, PartialEq, WasmType)]
struct Normal {
    value: u64,
    values: Vec<i8>,
}

#[test]
fn normal_read() {
    let mut reader = Mock::with(&[0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 2]);
    let normal = Normal::read(&mut reader).expect("valid value to be in memory");

    assert_eq!(normal.value, 1u64 << 24);
    assert_eq!(&normal.values, &[0, 1, 2]);
}

#[test]
fn normal_write() {
    let mut writer = Mock::new();
    let normal = Normal {
        value: 69,
        values: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    };

    normal.write(&mut writer).expect("write to be successful");
    assert_eq!(writer.memory.len(), 8 + 11 + 4);
    assert_eq!(Some(writer.memory.len() as u32), normal.size());

    let normal_read = Normal::read(&mut writer).expect("read to be successful");
    assert_eq!(normal_read, normal);
}

#[derive(WasmType)]
enum TriEnum {
    A,
    B(u32, u32),
    C { x: i8 },
}

#[test]
fn tri_enum_read() {
    let mut reader = Mock::with(b"\x00\x00\x00\x00\x01\0\0\0\x02\0\0\0\x03\0\0\0\x02\0\0\0\xFF");
    let tri_1 = TriEnum::read(&mut reader).expect("valid value");
    let tri_2 = TriEnum::read(&mut reader).expect("valid value");
    let tri_3 = TriEnum::read(&mut reader).expect("valid value");

    assert!(matches!(tri_1, TriEnum::A));
    assert!(matches!(tri_2, TriEnum::B(2, 3)));
    assert!(matches!(tri_3, TriEnum::C { x: -1 }));

    assert_eq!(tri_1.size(), Some(4));
    assert_eq!(tri_2.size(), Some(4 + 4 + 4));
    assert_eq!(tri_3.size(), Some(4 + 1));
}

#[test]
fn tri_enum_write() {
    let mut writer = Mock::new();
    let tri_1 = TriEnum::A;
    let tri_2 = TriEnum::B(2, 3);
    let tri_3 = TriEnum::C { x: 71 };

    tri_1.write(&mut writer).expect("write to be valid");
    tri_2.write(&mut writer).expect("write to be valid");
    tri_3.write(&mut writer).expect("write to be valid");

    assert_eq!(
        &writer.memory,
        b"\x00\x00\x00\x00\x01\0\0\0\x02\0\0\0\x03\0\0\0\x02\0\0\0\x47"
    );
}
