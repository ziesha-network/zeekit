use super::*;

#[derive(Clone)]
pub struct Number(pub LinearCombination<BellmanFr>, pub Option<BellmanFr>);
impl Number {
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
    pub fn add_num(&mut self, coeff: BellmanFr, num: &AllocatedNum<BellmanFr>) {
        self.0 = self.0.clone() + (coeff, num.get_variable());
        self.1 = if let Some(v) = self.1 {
            num.get_value().map(|n| n * coeff + v)
        } else {
            None
        };
    }
    pub fn constant<CS: ConstraintSystem<BellmanFr>>(v: BellmanFr) -> Number {
        Number(
            LinearCombination::<BellmanFr>::zero() + (v, CS::one()),
            Some(v),
        )
    }
    pub fn zero() -> Number {
        Number(
            LinearCombination::<BellmanFr>::zero(),
            Some(BellmanFr::zero()),
        )
    }
    pub fn one<CS: ConstraintSystem<BellmanFr>>() -> Number {
        Number(
            LinearCombination::<BellmanFr>::zero() + CS::one(),
            Some(BellmanFr::one()),
        )
    }
    pub fn mul<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        other: &Number,
    ) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
        let result = AllocatedNum::alloc(&mut *cs, || {
            self.get_value()
                .zip(other.get_value())
                .map(|(a, b)| a * b)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "",
            |lc| lc + self.get_lc(),
            |lc| lc + other.get_lc(),
            |lc| lc + result.get_variable(),
        );
        Ok(result)
    }
    pub fn compress<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
        self.mul::<CS>(cs, &Self::one::<CS>())
    }
}

impl Add for Number {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(
            self.0 + &other.0,
            self.1.zip(other.1).map(|(slf, othr)| slf + othr),
        )
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self(
            self.0 - &other.0,
            self.1.zip(other.1).map(|(slf, othr)| slf - othr),
        )
    }
}

impl From<AllocatedNum<BellmanFr>> for Number {
    fn from(a: AllocatedNum<BellmanFr>) -> Self {
        Self(
            LinearCombination::<BellmanFr>::zero() + a.get_variable(),
            a.get_value(),
        )
    }
}

impl From<(BellmanFr, AllocatedNum<BellmanFr>)> for Number {
    fn from(a: (BellmanFr, AllocatedNum<BellmanFr>)) -> Self {
        Self(
            LinearCombination::<BellmanFr>::zero() + (a.0, a.1.get_variable()),
            a.1.get_value().map(|v| v * a.0),
        )
    }
}

impl From<AllocatedBit> for Number {
    fn from(a: AllocatedBit) -> Self {
        Self(
            LinearCombination::<BellmanFr>::zero() + a.get_variable(),
            a.get_value()
                .map(|b| BellmanFr::from(if b { 1 } else { 0 })),
        )
    }
}

impl From<UnsignedInteger> for Number {
    fn from(a: UnsignedInteger) -> Self {
        Self(
            LinearCombination::<BellmanFr>::zero() + a.get_lc(),
            a.get_value(),
        )
    }
}
