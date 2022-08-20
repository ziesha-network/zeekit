use super::*;

#[derive(Clone)]
pub struct WrappedLc(pub LinearCombination<BellmanFr>, pub Option<BellmanFr>);
impl WrappedLc {
    pub fn get_lc(&self) -> &LinearCombination<BellmanFr> {
        &self.0
    }
    pub fn get_value(&self) -> Option<BellmanFr> {
        self.1
    }
    pub fn add_constant<CS: ConstraintSystem<BellmanFr>>(&mut self, num: BellmanFr) {
        self.0 = self.0.clone() + (num, CS::one());
        self.1 = self.1.map(|v| v + num);
    }
    pub fn add_num(&mut self, num: &AllocatedNum<BellmanFr>) {
        self.0 = self.0.clone() + num.get_variable();
        self.1 = if let Some(v) = self.1 {
            num.get_value().map(|n| n + v)
        } else {
            None
        };
    }
    pub fn alloc_num(a: AllocatedNum<BellmanFr>) -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + a.get_variable(),
            a.get_value(),
        )
    }
    pub fn constant<CS: ConstraintSystem<BellmanFr>>(v: BellmanFr) -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + (v, CS::one()),
            Some(v),
        )
    }
    pub fn zero() -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero(),
            Some(BellmanFr::zero()),
        )
    }
}

impl Add for WrappedLc {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(
            self.0 + &other.0,
            self.1.zip(other.1).map(|(slf, othr)| slf + othr),
        )
    }
}

impl Sub for WrappedLc {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self(
            self.0 - &other.0,
            self.1.zip(other.1).map(|(slf, othr)| slf - othr),
        )
    }
}
