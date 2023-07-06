# bubblesort_ten
A halo2 circuit verifying that a list of ten unsigned 32-bit integers was sorted according to the bubblesort algorithm.  A practice project for HyperOracle.

## The Basic Logic
The BubbleSort algorithm sorts a list by successively comparing two neighboring entries in a list, and swapping them if they're out of order.  In general, a circuit must allow a verifier to verify a correct computation trace using only polynomial constraints over finite field elements.  A correct computation trace for a bubblesort algorithm might look something like this:

|   state   | considering |    decision                 |
|:---------:|:-----------:|:---------------------------:|
| [8, 5, 9] | (8, 5)      | 8 > 5,  so swap             |
| [5, 8, 9] | (8, 9)      | not (8 > 9),  so don't swap |
| [5, 8, 9] |             |         ouput               |

However, there is a problem here.  Since the "natural" order on the integers mod p (for some prime p) is not compatible with addition mod p (and more generally, non-trivial finite groups cannot be ordered groups), there is no easy or natural way to write the relation "x > y" as a polynomial constraint.  We know that one exists: by Lagrange interpolation, any function from a finite field to itself is polynomial, hence any relation can be described as a polynomial constraint.  However, in all likelihood, the polynomial p satisfying "p(x, y) = 0 if and only if x < y" is likely of degree roughly 2^{256} in both x and y, and would be incredibly expensive to find and use in a custom gate.

Therefore we need some clever strategy to constrain the swaps so that the verifier can be convinced that each swap was correctly performed.  Consider the difference between two successive (field element) entries in the list, call them a and b.  We are given that a and b lie in the range [0, ..., 2^{32} - 1].  Now consider a - b and b - a.  One of them is equal |a - b|, which also lies in the range [0, ..., 2^{32}-1].  The other is equal to -|a - b|, which lies in the range [p - 2^{32} + 1, ..., p - 1, 0].  Since the field is large (p is roughly 2^{256}), none of the elements in the latter range (except 0) is equal to a sum of the form x_0 + 2x_1 + 4x_2 + ... + 2^{31}x_{31}, where each x_i is equal to 0 or 1.  Thus only |a - b| can be expressed this way.  

Now |a - b| is either equal to a - b if a > b, in which case a swap is needed; or b - a if a <= b, in which case a swap is not needed.  Again, since the field is large, |a - b| is not equal to both unless a = b, in which case either swapping or not swapping is permissible.

Let (a', b') be the result of applying the conditional swap to (a, b).  We should have a' = b if a > b and a' = a otherwise; and b' = a if a > b, and b' = b otherwise.  Then our strategy for verifying a correct swap is the following:
- Have the prover tell you whether they plan on swapping a and b, using an auxiliary value x = 1 if a > b, and x = 0 otherwise. Constrain x to be either 0 or 1 with the constraint x^2 - x = 0.
- Have the prover decompose |a - b| into bits x_0, x_1, ..., x_{31}. Constrain (x_i)^2 - x_i = 0 for each i.
- Constrain that
  - x_0 + 2x_1 + ... + 2x_{31} = b - a if x = 0
  - x_0 + 2x_1 + ... + 2x_{31} = a - b if x = 1
  - a' = a if x = 0
  - a' = b if x = 1
  - b' = b if x = 0
  - b' = a if x = 1

Now, a relation of the form "s = (t if u = 0, v if u = 1)" can be written as the polynomial constraint s = (1-u)t + uv.  So all the above constraints are polynomial, and there exists a satisfying assignment (a, b, a', b', x, x_0, x_1, ..., x_{31}) if and only if (a', b') is the result of applying a conditional swap to (a,b).

## How it Works: a Small Example

For simplicity, let's consider an example where the list is of length three instead of ten.  The circuit will have 3 + 2 advice columns, one fixed column, 2 + (3-1) selectors, and one instance column, for a total of 11 columns.

### Columns

These columns are given different, more descriptive names in the code.  They've been given more concise names here for the purposes of fitting images of the table onto the screen.

#### Advice Columns
The first three advice columns (a_0, a_1, and a_2) store the current state of the list in the process of sorting.  The "swap" advice column declares the prover's intention to swap the entries at two neighboring indices under consideration.  The "diff" advice column is where the prover fills in a binary decomposition of the difference between the two neighboring entries.  This helps to verify the correctness of the prover's entry into the "swap" advice column--more on this later.

#### Fixed Columns
The only fixed column (that is not also a selector) is the 2^n column, which holds all powers of 2 from 2^0 to 2^{31}.

#### Selectors
There are two "bit selectors," called "swap bit" and "diff bit."  They are in charge of ensuring that the prover-given entries in the "swap" and "diff" columns are all either 0 or 1.

The other selectors are the "swap selectors," here labeled as s_0 and s_1.  If s_i is enabled, it means that, at this stage in the bubblesort algorithm, indices i and i+1 are being considered for a swap.

#### Instance Columns
This holds the expected output of the computation.  It doesn't belong to any region, instead having an absolute location outside the regions of the circuit.  In this case it's only used for testing.

### Synthesis

Suppose that the list we want to sort is [8, 5, 9].  The expected output of a sort would be [5, 8, 9], which the verifier will write to the instance column.

First, the prover assigns the input to the first region.  That is, they assign 8 to advice column a_0, 5 to advice column a_1, and 9 to advice column a_2.  At this stage, nothing is constrained, so no selectors are enabled.  The only reason for this step is technical: to assign one swap we need to copy a list of assigned cells that correspond to the current state of the list.  Therefore, we have to assign some cells before beginning to assign swaps.

[Assigning Input](images/assigning_input.png)

The next region corresponds to the first swap, and is assigned accordingly.  The output from the previous assignment is copied to advice columns a_0, a_1, a_2 using copy constraints.  Offline, the prover fills in swap with 1, since 8 > 5, calculates the difference |8 - 5| = 3 = 110...0 in binary, and assigns these bits to the diff_bits column.  The 2^n fixed column is filled in with powers of 2 from 2^0 to 2^{31}.  Since this column is fixed, the prover cannot assign to this column, and the assignment instead happens as part of the setup.  The bit selectors and the swap selector s_0 are enabled, since the first conditional swap should be applied to indices 0 and 1.  Similarly, the prover has no control over this.

[Assigning First Swap](images/assigning_first_swap.png)

The image below shows the entries constrained by the "swap gate."

[Swap Gate](images/swap_gate.png)

[Bit Gates](images/bit_gates.png)

[Difference Gate](images/difference_gate.png)

[Assigning Second Swap](images/assigning_second_swap.png)

In reality, another "pass" consisting of two more regions would be added before the output is checked since, in the worst case, a three-element list needs two passes to be sorted.  However, for the purposes of this readme, we'll just skip to the final phase of output checking.

[Checking Output](images/checking_output.png)
