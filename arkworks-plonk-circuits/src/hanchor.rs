// *Submission by S.Yoon as a coding challenge with bountiful comments
// addressing his thoughts. Code taken from vanchor.rs and modified from there.
// It appears we mean to use ZK-Garage/plonk implementation.

// HAnchor (Hyper Anchor) is the multi-asset deposit/withdraw/transfer shielded
// pool It supports join split transactions across multiple assets, meaning
// you can take unspent deposits in the pool and join them together, split them,
// and any combination of the two, while maintaining the net amount for each
// asset & chain.

// The inputs to the HAnchor are unspent outputs we want to spend (we are
// spending the inputs), and we create outputs which are new, unspent UTXOs. We
// create commitments for each output and these are inserted into merkle trees.

// The HAnchor is also a bridged system. It takes as a public input
// a set of merkle roots that it will use to verify the membership
// of unspent deposits within. The HAnchor prevents double-spending
// through the use of a public input chain identifier `chain_id`.

// We will take inputs and do a merkle tree reconstruction for each input.
// Then we will verify that the reconstructed root from each input's
// membership path is within a set of public merkle roots.

use ark_ec::models::TEModelParameters;
use ark_ff::PrimeField;
use arkworks_native_gadgets::merkle_tree::Path;
use arkworks_plonk_gadgets::{
	add_public_input_variable, add_public_input_variables, merkle_tree::PathGadget,
	poseidon::FieldHasherGadget, set::SetGadget,
};
use plonk_core::{circuit::Circuit, constraint_system::StandardComposer, error::Error};

pub struct HyperAnchorCircuit<
	F: PrimeField,
	P: TEModelParameters<BaseField = F>,
	HG: FieldHasherGadget<F, P>,
	// Tree height
	const N: usize,
	// Size of the root set (bridge length)
	const M: usize,
	// Number of inputs
	const INS: usize,
	// Number of outputs
	const OUTS: usize,
> {
	// sum of input amounts + public amount == sum of output amounts
	public_amount: F,   // Public
	public_asset_id: F, // Public // *Newly added for HAnchor
	public_chain_id: F, // Public

	// Input transactions
	in_amounts: [F; INS],
	in_blindings: [F; INS],
	in_nullifier_hashes: [F; INS], // Public
	in_private_keys: [F; INS],
	in_paths: [Path<F, HG::Native, N>; INS],
	in_indices: [F; INS],
	in_root_set: [F; M],

	// Output transactions
	out_amounts: [F; OUTS],
	out_asset_ids: [F; OUTS], // *Newly added for HAnchor
	out_blindings: [F; OUTS],
	out_chain_ids: [F; OUTS],
	out_public_keys: [F; OUTS],
	out_commitments: [F; OUTS], // Public

	// Arbitrary data to be added to the transcript
	arbitrary_data: F, // Public

	// All the hashers used in this circuit
	// Used for hashing private_key -- width 2
	public_key_hasher: HG::Native,
	// Used for hashing nodes in the tree -- width 3
	tree_hasher: HG::Native,
	// Used for creating leaf signature and the nullifier hash -- width 4
	signature_hasher: HG::Native,
	// Used for creating leaf -- width 5
	leaf_hasher: HG::Native,
}

impl<F, P, HG, const N: usize, const M: usize, const INS: usize, const OUTS: usize>
	HyperAnchorCircuit<F, P, HG, N, M, INS, OUTS>
where
	F: PrimeField,
	P: TEModelParameters<BaseField = F>,
	HG: FieldHasherGadget<F, P>,
{
	pub fn new(
		public_amount: F,
		public_asset_id: F, // *Newly added for HAnchor
		public_chain_id: F,
		in_amounts: [F; INS],
		in_blindings: [F; INS],
		in_nullifier_hashes: [F; INS],
		in_private_keys: [F; INS],
		in_paths: [Path<F, HG::Native, N>; INS],
		in_indices: [F; INS],
		in_root_set: [F; M],
		out_amounts: [F; OUTS],
		out_asset_ids: [F; OUTS], // *Newly added for HAnchor
		out_blindings: [F; OUTS],
		out_chain_ids: [F; OUTS],
		out_public_keys: [F; OUTS],
		out_commitments: [F; OUTS],
		arbitrary_data: F,
		public_key_hasher: HG::Native,
		tree_hasher: HG::Native,
		signature_hasher: HG::Native,
		leaf_hasher: HG::Native,
	) -> Self {
		Self {
			public_amount,
			public_asset_id, // *Newly added for HAnchor
			public_chain_id,
			in_amounts,
			in_blindings,
			in_nullifier_hashes,
			in_private_keys,
			in_paths,
			in_indices,
			in_root_set,
			out_amounts,
			out_asset_ids, // *Newly added for HAnchor
			out_blindings,
			out_chain_ids,
			out_public_keys,
			out_commitments,
			arbitrary_data,
			public_key_hasher,
			tree_hasher,
			signature_hasher,
			leaf_hasher,
		}
	}
}

impl<F, P, HG, const N: usize, const M: usize, const INS: usize, const OUTS: usize> Circuit<F, P>
	for HyperAnchorCircuit<F, P, HG, N, M, INS, OUTS>
where
	F: PrimeField,
	P: TEModelParameters<BaseField = F>,
	HG: FieldHasherGadget<F, P>,
{
	const CIRCUIT_ID: [u8; 32] = [0xff; 32];

	fn gadget(&mut self, composer: &mut StandardComposer<F, P>) -> Result<(), Error> {
		// Initialize public inputs
		let public_amount = add_public_input_variable(composer, self.public_amount);
		let arbitrary_data = add_public_input_variable(composer, self.arbitrary_data);
		// Allocate nullifier hashes
		let nullifier_hash_vars =
			add_public_input_variables(composer, self.in_nullifier_hashes.to_vec());
		// Allocate output commitments
		let commitment_vars = add_public_input_variables(composer, self.out_commitments.to_vec());
		let public_asset_id = add_public_input_variable(composer, self.public_asset_id);
		let public_chain_id = add_public_input_variable(composer, self.public_chain_id);
		let set_gadget = SetGadget::from_native(composer, self.in_root_set.to_vec());

		// Initialize hashers
		let pk_hasher_gadget: HG =
			FieldHasherGadget::<F, P>::from_native(composer, self.public_key_hasher.clone());
		let tree_hasher_gadget: HG =
			FieldHasherGadget::<F, P>::from_native(composer, self.tree_hasher.clone());
		let sig_hasher_gadget: HG =
			FieldHasherGadget::<F, P>::from_native(composer, self.signature_hasher.clone());
		let leaf_hasher_gadget: HG =
			FieldHasherGadget::<F, P>::from_native(composer, self.leaf_hasher.clone());

		// Sum of input amounts + public amount must equal output amounts at the end
		let mut input_sum = public_amount;
		let mut output_sum = composer.zero_var();

		// General strategy
		// 1. Reconstruct the commitments (along the way reconstruct other values)
		// 2. Reconstruct the target merkle root with the input's merkle path
		// 3. Verify that the target merkle root is within the root set
		// 4. Sum the input amounts
		for i in 0..INS {
			// Private inputs for each input UTXO being spent
			let in_private_key_i = composer.add_input(self.in_private_keys[i]);
			let in_amount_i = composer.add_input(self.in_amounts[i]);
			let in_blinding_i = composer.add_input(self.in_blindings[i]);
			let in_index_i = composer.add_input(self.in_indices[i]);
			let path_gadget =
				PathGadget::<F, P, HG, N>::from_native(composer, self.in_paths[i].clone());

			// Computing the public key, which is done just by hashing the private key
			let calc_public_key = pk_hasher_gadget.hash(composer, &[in_private_key_i])?;

			let calc_subleaf = leaf_hasher_gadget.hash(composer, &[
				// *Separate subleaf hasher gadget needed? probably not.
				public_chain_id,
				calc_public_key,
				in_blinding_i,
			])?;

			// Computing the leaf
			let calc_leaf =
				leaf_hasher_gadget.hash(composer, &[calc_subleaf, in_amount_i, public_asset_id])?;

			// Computing the signature: sign(private_key, leaf, input_index)
			let calc_signature =
				sig_hasher_gadget.hash(composer, &[in_private_key_i, calc_leaf, in_index_i])?;

			// Computing the nullifier hash. This is used to prevent spending
			// already spent UTXOs.
			let calc_nullifier =
				sig_hasher_gadget.hash(composer, &[calc_leaf, in_index_i, calc_signature])?;

			// Checking if the passed nullifier hash is the same as the calculated one
			// Optimized version of allocating public nullifier input and constraining
			// to the calculated one.
			composer.assert_equal(calc_nullifier, nullifier_hash_vars[i]);

			// Calculate the root hash
			let calc_root_hash =
				path_gadget.calculate_root(composer, &calc_leaf, &tree_hasher_gadget)?;

			// Check if calculated root hash is in the set
			// Note that if `in_amount_i = 0` then the input is a
			// "dummy" input, so the check is not needed.  The
			// `check_set_membership_is_enabled` function accounts for this.
			let is_member =
				set_gadget.check_set_membership_is_enabled(composer, calc_root_hash, in_amount_i);
			composer.constrain_to_constant(is_member, F::one(), None); // *Cool!

			// Finally add the amount to the sum
			// TODO: Investigate improvements to accumulating sums
			input_sum = composer.arithmetic_gate(|gate| {
				gate.witness(input_sum, in_amount_i, None)
					.add(F::one(), F::one())
			});
		}

		// Check all the nullifiers are unique to prevent double-spending
		// TODO: Investigate checking nullifier uniqueness this check to the application
		// side
		for i in 0..INS {
			for j in (i + 1)..INS {
				let result =
					composer.is_eq_with_output(nullifier_hash_vars[i], nullifier_hash_vars[j]);
				composer.assert_equal(result, composer.zero_var());
			}
		}

		for i in 0..OUTS {
			let out_chain_id_i = composer.add_input(self.out_chain_ids[i]);
			let out_public_key_i = composer.add_input(self.out_public_keys[i]);
			let out_blinding_i = composer.add_input(self.out_blindings[i]);
			let out_amount_i = composer.add_input(self.out_amounts[i]);
			let out_asset_id_i = composer.add_input(self.out_asset_ids[i]);
			// Calculate the leaf commitment
			let calc_subleaf = leaf_hasher_gadget.hash(composer, &[
				out_chain_id_i,
				out_public_key_i,
				out_blinding_i,
			])?;

			let calc_leaf =
				leaf_hasher_gadget.hash(composer, &[calc_subleaf, out_amount_i, out_asset_id_i])?;

			// Check if calculated leaf is the same as the passed one
			composer.assert_equal(calc_leaf, commitment_vars[i]);

			// Each amount should not be greater than the limit constant
			// TODO: The field size can be gotten as F::size_in_bits()
			// What is the correct transaction limit?
			// Each amount should be less than (field size)/2 to prevent
			// overflow, which suggests that F::size_in_bits() - 1 would
			// be small enough.  Maybe use F::size_in_bits() - 100 to be safe?
			composer.range_gate(out_amount_i, 254);

			// Add in to the sum
			output_sum = composer.arithmetic_gate(|gate| {
				gate.witness(output_sum, out_amount_i, None)
					.add(F::one(), F::one())
			});
		}

		composer.assert_equal(input_sum, output_sum);

		// *This squared data hasn't been used/constrained. Looks like this gadget will
		// work w/o it?
		let _arbitrary_data_squared = composer.arithmetic_gate(|gate| {
			gate.witness(arbitrary_data, arbitrary_data, None)
				.mul(F::one())
		});

		Ok(())
	}

	fn padded_circuit_size(&self) -> usize {
		1 << 21 // *Learn how to count circuit sizes.
		 // I think an input variable, arithmetic gate, constraint each requires
		 // unit cost (1) and a constant costs nothing (0)? Wouldn't the circuit
		 // size depend on INS and OUTS because of the summing of amounts?
	}
}
