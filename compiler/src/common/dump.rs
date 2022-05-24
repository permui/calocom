pub trait Dump {
    fn dump_string(&self) -> String;
}

impl<T> Dump for &T
where
    T: Dump,
{
    fn dump_string(&self) -> String {
        (*self).dump_string()
    }
}
