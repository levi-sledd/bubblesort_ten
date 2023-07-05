use std::{marker::PhantomData, cmp::*};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*,
    poly::Rotation,
};

#[derive(Clone, Debug)]
struct BubbleSortConfig {
    pub state_columns: [Column<Advice>; 10],
    pub difference_bits_column: Column<Advice>,
    pub should_swap_column: Column<Advice>,

    pub swap_selectors: [Selector; 9],
    pub difference_bit_selector: Selector,
    pub should_swap_bit_selector: Selector,

    pub powers_of_two: Column<Fixed>,

    pub instance_column_for_testing: Column<Instance>,
}

#[derive(Clone, Debug)]
struct BubbleSortChip<F: FieldExt> {
    config: BubbleSortConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BubbleSortChip<F> {
    pub fn construct(config: BubbleSortConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> BubbleSortConfig {
        let state_columns = [0; 10].map(|_| cs.advice_column());
        for i in 0..10 {
            cs.enable_equality(state_columns[i]);
        }
        let difference_bits_column = cs.advice_column();
        let should_swap_column = cs.advice_column();

        let swap_selectors = [0; 9].map(|_| cs.selector());
        let difference_bit_selector = cs.selector();
        let should_swap_bit_selector = cs.selector();

        let powers_of_two = cs.fixed_column();

        let instance_column_for_testing = cs.instance_column();
        cs.enable_equality(instance_column_for_testing);

        for i in 0..9 { 
            cs.create_gate("swap gate", |cs| {
                let may_swap = cs.query_selector(swap_selectors[i]);
                let should_swap = cs.query_advice(should_swap_column, Rotation(0));
                let should_not_swap = Expression::Constant(F::from(1)) - should_swap.clone();

                let a = cs.query_advice(state_columns[i], Rotation(0));
                let b = cs.query_advice(state_columns[i+1], Rotation(0));

                let a_prime = cs.query_advice(state_columns[i], Rotation(1));
                let b_prime = cs.query_advice(state_columns[i+1], Rotation(1));


                // If a and b may be swapped, then a' = a if they should not be swapped, and
                // b if they should; b' = b if they should not be swapped, and a if they should.
                vec![may_swap.clone() * (a_prime.clone() -
                        (should_not_swap.clone() * a.clone() + should_swap.clone() * b.clone())),
                    may_swap.clone() * (b_prime.clone() - 
                        (should_not_swap.clone() * b.clone() + should_swap.clone() * a.clone()))]

            });
        }

        // Enforces that something assigned to the "difference bits" column is actually
        // a bit.
        cs.create_gate("difference bit gate", |cs| {
            let should_be_bit = cs.query_selector(difference_bit_selector);
            let x = cs.query_advice(difference_bits_column, Rotation(0));

            vec![should_be_bit * x.clone() * (Expression::Constant(F::from(1)) - x.clone())]
        });

        // Enforces that should_swap is a bit.
        cs.create_gate("should swap bit gate", |cs| {
            let should_be_bit = cs.query_selector(should_swap_bit_selector);
            let x = cs.query_advice(should_swap_column, Rotation(0));

            vec![should_be_bit * x.clone() * (Expression::Constant(F::from(1)) - x.clone())]
        });

        for i in 0..9 {
            cs.create_gate("difference binary", |cs| {
                let is_binary_for = cs.query_selector(swap_selectors[i]);

                let a = cs.query_advice(state_columns[i], Rotation(0));
                let b = cs.query_advice(state_columns[i+1], Rotation(0));
                let should_swap = cs.query_advice(should_swap_column, Rotation(0));
                let should_not_swap = Expression::Constant(F::from(1)) - should_swap.clone();

                // The difference |a-b| should be a-b if should_swap is 1, otherwise b-a.
                let difference = should_swap.clone() * (a.clone() - b.clone()) 
                    + should_not_swap.clone() * (b.clone() - a.clone());


                // binary_expansion = difference_bits[0] * 2^0 + ... + difference_bits[31] * 2^{31}
                let binary_expansion = (0..32)
                    .map(|j| { 
                        cs.query_advice(difference_bits_column, Rotation(j))
                        * cs.query_fixed(powers_of_two, Rotation(j))
                        }
                    )
                    .fold(
                        Expression::Constant(F::from(0)),
                        |acc, x| acc + x,
                    );

                // Enforces that binary_expansion = difference;
                // essentially, that the prover decomposed |a-b| using
                // only 32 bits.
                vec![is_binary_for * (difference - binary_expansion)]
            });
        }

        BubbleSortConfig {
            state_columns,
            difference_bits_column,
            should_swap_column,

            swap_selectors,
            difference_bit_selector,
            should_swap_bit_selector,

            powers_of_two,

            instance_column_for_testing,
        }
    }

    pub fn assign_input(
        &self,
        mut layouter: impl Layouter<F>,
        state: [u32; 10],
    ) -> Result<([u32; 10], Vec<AssignedCell<F, F>>), Error> {
        layouter.assign_region(
            || "input row: no selectors/constraints enabled",
            |mut region| {
                let input_cells: Vec<AssignedCell<F, F>> = (0..10)
                    .map(|i| {
                            region.assign_advice(
                                || "input entry", 
                                self.config.state_columns[i], 
                                0, 
                                || Value::known(F::from(state[i] as u64))
                            ).unwrap()
                        }
                    ).collect();
                Ok((state, input_cells))
            }
        )
    }

    pub fn assign_conditional_swap(
        &self,
        mut layouter: impl Layouter<F>,
        state: [u32; 10],
        state_cells: Vec<AssignedCell<F, F>>,
        i: usize,
    ) -> Result<([u32; 10], Vec<AssignedCell<F, F>>), Error> {
        // Computations done by an honest prover
        // outside the circuit.
        let a = state[i] as u64;
        let b = state[i+1] as u64;
        let a_prime = min(a, b);
        let b_prime = max(a, b);

        let difference = (b_prime - a_prime) as u32;
        let difference_bits = u32_to_u64_bit_array(&difference);
        let should_swap = if a > b { 1 } else { 0 };

        let new_state_cells = layouter.assign_region(
            || "conditional swap", 
            |mut region| {
                // Start assigning by copying "state_cells" to row 0 of the current region.
                for k in 0..10 {
                    let _copied_cells = state_cells[k].copy_advice(
                        || "state before", 
                        &mut region,
                        self.config.state_columns[k],
                        0,
                    )?;
                }

                // Enforces the swap constraints at i and i+1, that difference_bits
                // are in fact bits, and that should_swap is a bit.
                self.config.swap_selectors[i].enable(&mut region, 0)?;
                self.config.should_swap_bit_selector.enable(&mut region, 0)?;
                for j in 0..32 {
                    self.config.difference_bit_selector.enable(&mut region, j)?;
                }

                // Assigns powers of 2 to the fixed column.
                let two = 2 as u64;
                let _powers_of_two_cells: Vec<AssignedCell<F, F>> = (0..32)
                    .map(|j| region.assign_fixed(
                            || "powers of two", 
                            self.config.powers_of_two, 
                            j,
                            || Value::known(F::from(two.pow(j as u32))),
                        ).unwrap()
                    )
                    .collect();

                // Assigns cells in the difference_bits advice column from 
                // the prover's pre-computed bit decomposition of |a-b|,
                // where a and b are the u32s being considered for a swap.
                let _difference_bits_cells: Vec<AssignedCell<F, F>> = (0..32)
                    .map(|j| 
                        region.assign_advice(
                            || "bit of difference", 
                            self.config.difference_bits_column, 
                            j, 
                            || Value::known(F::from(difference_bits[j]))
                        )
                        .unwrap()
                    )
                    .collect();
                
                // Assigns the should_swap bit to row 0 of the should_swap column.
                let _should_swap_cell = region.assign_advice(
                    || "should swap", 
                    self.config.should_swap_column, 
                    0, 
                    || Value::known(F::from(should_swap)),
                )?;
                
                // Now we assign the next row, representing the state after
                // the swap.  We also have to collect these into a vector
                // to return later.
                // All entries not under consideration for a swap should
                // be copied from the previous state.

                let mut new_state_cells: Vec<AssignedCell<F, F>> = Vec::new();
                for k in 0..i {
                    new_state_cells.push(
                        state_cells[k].copy_advice(
                            || "state before", 
                            &mut region,
                            self.config.state_columns[k],
                            1,
                        ).unwrap()
                    );
                }

                let a_prime_cell = region.assign_advice(
                    || "a'", 
                    self.config.state_columns[i],
                    1,
                    || Value::known(F::from(a_prime)),
                )?;
                new_state_cells.push(a_prime_cell);

                let b_prime_cell = region.assign_advice(
                    || "b'", 
                    self.config.state_columns[i+1],
                    1,
                    || Value::known(F::from(b_prime)),
                )?;
                new_state_cells.push(b_prime_cell);

                for k in i+2..10 {
                    new_state_cells.push(
                        state_cells[k].copy_advice(
                            || "state before", 
                            &mut region,
                            self.config.state_columns[k],
                            1,
                        ).unwrap()
                    );
                }

                Ok(new_state_cells)
            },
        )?;

        let mut new_state = state.clone();
        new_state[i] = a_prime as u32;
        new_state[i+1] = b_prime as u32;
        Ok((new_state, new_state_cells))
    }

    pub fn assign_pass(
        &self,
        mut layouter: impl Layouter<F>,
        mut state: [u32; 10],
        mut state_cells: Vec<AssignedCell<F, F>>,
        k: usize,
    ) -> Result<([u32; 10], Vec<AssignedCell<F, F>>), Error> {
        for i in 0..(9-k) {
            (state, state_cells) = self.assign_conditional_swap(
                layouter.namespace(|| "conditional swap {i}"), 
                state, 
                state_cells, 
                i,
            )?;
            println!("{:?}", state);
        }
        
        Ok((state, state_cells))
    }

    pub fn check_output(
        &self,
        mut layouter: impl Layouter<F>,
        output_cells: Vec<AssignedCell<F, F>>,
    ) ->  Result<(), Error> {
        for i in 0..10 {
            layouter.constrain_instance(
                output_cells[i].cell(), 
                self.config.instance_column_for_testing, 
                i,
            )?;
        }
        Ok(())
    }
}

#[derive(Default)]
struct BubbleSortCircuit<F> {
    input: [u32; 10],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for BubbleSortCircuit<F> {
    type Config = BubbleSortConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        BubbleSortChip::configure(meta)
    }

    fn synthesize(
        &self, 
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = BubbleSortChip::construct(config);

        let (mut state, mut state_cells) = 
            chip.assign_input(
                layouter.namespace(|| "input"),
                self.input
            )?;
        println!("{:?}", state);

        for k in 0..9 {
            (state, state_cells) = chip.assign_pass(
                layouter.namespace(|| "first pass"), 
                state, 
                state_cells,
                k,
            )?;
        }

        chip.check_output(
            layouter.namespace(|| "output"),
            state_cells,
        )?;

        Ok(())
    }
}

pub fn u32_to_u64_bit_array(input: &u32) -> [u64; 32] {
    let mut output: [u64; 32] = [0; 32];
    for i in 0..32 {
        output[i] = ((input >> i) % 2) as u64;
    }
    output
}

#[cfg(test)]

mod tests {
    use std::marker::PhantomData;

    use super::BubbleSortCircuit;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn test_all_passes() {
        let input: [u32; 10] = [9, 8, 7, 6, 5, 4, 3, 2, 1, 0];

        let circuit: BubbleSortCircuit<Fp> = BubbleSortCircuit {
            input,
            _marker: PhantomData,
        };

        let expected_output: [u32; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        
        let expected_output_field_elements: Vec<Fp> = expected_output
            .map(|i| Fp::from(i as u64))
            .into_iter()
            .collect();

        let prover = MockProver::run(
                11,
                &circuit,
                vec![expected_output_field_elements],
            )
            .unwrap();

        prover.assert_satisfied();
    }
}