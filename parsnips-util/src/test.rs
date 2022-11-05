#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + count!($($xs)*));
}

#[macro_export]
macro_rules! ne_byte_arr {
    ($($w:expr),+ $(,)?) => {
        {
            use parsnips_util::count;
            unsafe{ core::mem::transmute::<[u32; parsnips_util::count!($($w)*)], [u8; count!($($w)*)*4]>([$($w),+]) }
        }
    }
}
