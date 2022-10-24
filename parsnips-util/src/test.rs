#[macro_export]
macro_rules! le_byte_arr {
    ($($w:expr),+ $(,)?) => {
        [
            $(
                u32::to_le_bytes($w)[0],
                u32::to_le_bytes($w)[1],
                u32::to_le_bytes($w)[2],
                u32::to_le_bytes($w)[3],
            )*
        ]
    }
}
