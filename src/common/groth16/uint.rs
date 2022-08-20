use super::*;

pub struct UnsignedInteger {
    bits: Vec<AllocatedBit>,
    num: AllocatedNum<BellmanFr>,
}

impl UnsignedInteger {
    pub fn get_variable(&self) -> Variable {
        self.num.get_variable()
    }
    pub fn get_value(&self) -> Option<BellmanFr> {
        self.num.get_value()
    }
    pub fn bits(&self) -> &Vec<AllocatedBit> {
        &self.bits
    }
    pub fn num_bits(&self) -> usize {
        self.bits.len()
    }
    pub fn constrain<CS: ConstraintSystem<BellmanFr>>(
        cs: &mut CS,
        num: AllocatedNum<BellmanFr>,
        num_bits: usize,
    ) -> Result<Self, SynthesisError> {
        let mut bits = Vec::new();
        let mut coeff = BellmanFr::one();
        let mut all = LinearCombination::<BellmanFr>::zero();
        let bit_vals: Option<Vec<bool>> = num
            .get_value()
            .map(|v| v.to_le_bits().iter().map(|b| *b).collect());
        for i in 0..num_bits {
            let bit = AllocatedBit::alloc(&mut *cs, bit_vals.as_ref().map(|b| b[i]))?;
            all = all + (coeff, bit.get_variable());
            bits.push(bit);
            coeff = coeff.double();
        }
        cs.enforce(
            || "check",
            |lc| lc + &all,
            |lc| lc + CS::one(),
            |lc| lc + num.get_variable(),
        );

        Ok(Self { num, bits })
    }

    // ~198 constraints
    pub fn lt<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger,
    ) -> Result<AllocatedBit, SynthesisError> {
        assert_eq!(self.num_bits(), other.num_bits());
        let num_bits = self.num_bits();

        // Imagine a and b are two sigend (num_bits + 1) bits numbers
        let two_bits = BellmanFr::from(2).pow_vartime(&[num_bits as u64 + 1, 0, 0, 0]);
        let sub = AllocatedNum::alloc(&mut *cs, || {
            Ok(self
                .get_value()
                .zip(other.get_value())
                .map(|(a, b)| a - b + two_bits)
                .ok_or(SynthesisError::AssignmentMissing)?)
        })?;
        cs.enforce(
            || "",
            |lc| lc + self.get_variable() - other.get_variable() + (two_bits, CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + sub.get_variable(),
        );

        let sub_bits = UnsignedInteger::constrain(&mut *cs, sub, num_bits + 2)?;
        Ok(sub_bits.bits()[num_bits].clone())
    }

    pub fn gt<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger,
    ) -> Result<AllocatedBit, SynthesisError> {
        other.lt(cs, self)
    }

    pub fn lte<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger,
    ) -> Result<AllocatedBit, SynthesisError> {
        let gt = self.gt(cs, other)?;
        not(cs, gt)
    }

    pub fn gte<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        other: &UnsignedInteger,
    ) -> Result<AllocatedBit, SynthesisError> {
        let lt = self.lt(cs, other)?;
        not(cs, lt)
    }
}
