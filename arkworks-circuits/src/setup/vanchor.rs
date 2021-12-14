use crate::{
	circuit::vanchor::VAnchorCircuit as VACircuit,
	setup::common::{
		LeafCRHGadget, PoseidonCRH_x5_2, PoseidonCRH_x5_2Gadget, PoseidonCRH_x5_3Gadget,
		PoseidonCRH_x5_4, TreeConfig_x5, Tree_x5,
	},
};
use ark_bn254::Fr as Bn254Fr;
use ark_crypto_primitives::SNARK;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
	rand::{CryptoRng, RngCore},
	rc::Rc,
	vec::Vec,
};
use arkworks_gadgets::{
	arbitrary::vanchor_data::VAnchorArbitraryData,
	keypair::vanchor::Keypair,
	leaf::vanchor::{Private as LeafPrivateInput, Public as LeafPublicInput, VAnchorLeaf as Leaf},
	merkle_tree::Path,
	set::membership::{Private as SetPrivateInputs, SetMembership},
};
use arkworks_utils::{
	poseidon::PoseidonParameters,
	utils::{
		common::{
			setup_params_x5_2, setup_params_x5_3, setup_params_x5_4, setup_params_x5_5,
			verify_groth16, Curve,
		},
		keccak_256,
	},
};
use ethabi::{encode, Token};

#[derive(Debug)]
pub struct ExtData {
	pub recipient_bytes: Vec<u8>,
	pub relayer_bytes: Vec<u8>,
	pub ext_amount_bytes: Vec<u8>,
	pub fee_bytes: Vec<u8>,
	pub encrypted_output1_bytes: Vec<u8>,
	pub encrypted_output2_bytes: Vec<u8>,
}

impl ExtData {
	pub fn new(
		recipient_bytes: Vec<u8>,
		relayer_bytes: Vec<u8>,
		ext_amount_bytes: Vec<u8>,
		fee_bytes: Vec<u8>,
		encrypted_output1_bytes: Vec<u8>,
		encrypted_output2_bytes: Vec<u8>,
	) -> Self {
		Self {
			recipient_bytes,
			relayer_bytes,
			ext_amount_bytes,
			fee_bytes,
			encrypted_output1_bytes,
			encrypted_output2_bytes,
		}
	}

	fn into_abi(&self) -> Token {
		let recipient = Token::Bytes(self.recipient_bytes.clone());
		let ext_amount = Token::Bytes(self.ext_amount_bytes.clone());
		let relayer = Token::Bytes(self.relayer_bytes.clone());
		let fee = Token::Bytes(self.fee_bytes.clone());
		let encrypted_output1 = Token::Bytes(self.encrypted_output1_bytes.clone());
		let encrypted_output2 = Token::Bytes(self.encrypted_output2_bytes.clone());
		Token::Tuple(vec![
			recipient,
			relayer,
			ext_amount,
			fee,
			encrypted_output1,
			encrypted_output2,
		])
	}

	fn encode_abi(&self) -> Vec<u8> {
		let token = self.into_abi();
		let encoded_input = encode(&[token]);
		encoded_input
	}
}

pub fn get_hash_params<F: PrimeField>(
	curve: Curve,
) -> (
	PoseidonParameters<F>,
	PoseidonParameters<F>,
	PoseidonParameters<F>,
	PoseidonParameters<F>,
) {
	(
		setup_params_x5_2::<F>(curve),
		setup_params_x5_3::<F>(curve),
		setup_params_x5_4::<F>(curve),
		setup_params_x5_5::<F>(curve),
	)
}

#[derive(Clone)]
pub struct Utxos<F: PrimeField> {
	pub chain_ids: Vec<F>,
	pub amounts: Vec<F>,
	pub keypairs: Vec<Keypair<F, PoseidonCRH_x5_2<F>>>,
	pub leaf_privates: Vec<LeafPrivateInput<F>>,
	pub leaf_publics: Vec<LeafPublicInput<F>>,
	pub nullifiers: Vec<F>,
	pub commitments: Vec<F>,
}

pub struct VAnchorProverSetup<
	F: PrimeField,
	const TREE_DEPTH: usize,
	const M: usize,
	const INS: usize,
	const OUTS: usize,
> {
	params2: PoseidonParameters<F>,
	params3: PoseidonParameters<F>,
	params4: PoseidonParameters<F>,
	params5: PoseidonParameters<F>,
}

impl<
		F: PrimeField,
		const TREE_DEPTH: usize,
		const M: usize,
		const INS: usize,
		const OUTS: usize,
	> VAnchorProverSetup<F, TREE_DEPTH, M, INS, OUTS>
{
	pub fn new(
		params2: PoseidonParameters<F>,
		params3: PoseidonParameters<F>,
		params4: PoseidonParameters<F>,
		params5: PoseidonParameters<F>,
	) -> Self {
		Self {
			params2,
			params3,
			params4,
			params5,
		}
	}

	pub fn new_utxos<R: RngCore>(
		&self,
		chain_ids: Vec<F>,
		amounts: Vec<F>,
		rng: &mut R,
	) -> Utxos<F> {
		let keypairs = Self::setup_keypairs(amounts.len(), rng);
		let (commitments, nullifiers, leaf_privates, leaf_publics) =
			self.setup_leaves(&chain_ids, &amounts, &keypairs, rng);

		Utxos {
			chain_ids,
			amounts,
			keypairs,
			leaf_privates,
			leaf_publics,
			nullifiers,
			commitments,
		}
	}

	pub fn setup_random_circuit<R: RngCore>(
		self,
		rng: &mut R,
	) -> VACircuit<
		F,
		PoseidonCRH_x5_2<F>,
		PoseidonCRH_x5_2Gadget<F>,
		TreeConfig_x5<F>,
		LeafCRHGadget<F>,
		PoseidonCRH_x5_3Gadget<F>,
		TREE_DEPTH,
		INS,
		OUTS,
		M,
	> {
		let public_amount = F::rand(rng);
		let recipient = F::rand(rng);
		let relayer = F::rand(rng);
		let ext_amount = F::rand(rng);
		let fee = F::rand(rng);

		let in_chain_id = F::rand(rng);
		let in_amounts = vec![F::rand(rng); INS];
		let out_chain_ids = vec![F::rand(rng); OUTS];
		let out_amounts = vec![F::rand(rng); OUTS];

		let (circuit, ..) = self.setup_circuit_with_data(
			public_amount,
			recipient.into_repr().to_bytes_le(),
			relayer.into_repr().to_bytes_le(),
			ext_amount.into_repr().to_bytes_le(),
			fee.into_repr().to_bytes_le(),
			in_chain_id,
			in_amounts,
			out_chain_ids,
			out_amounts,
			rng,
		);

		circuit
	}

	pub fn setup_circuit_with_input_utxos<R: RngCore>(
		self,
		public_amount: F,
		recipient: Vec<u8>,
		relayer: Vec<u8>,
		ext_amount: Vec<u8>,
		fee: Vec<u8>,
		// Input transactions
		in_utxos: Utxos<F>,
		// Output data
		out_chain_ids: Vec<F>,
		out_amounts: Vec<F>,
		rng: &mut R,
	) -> (
		VACircuit<
			F,
			PoseidonCRH_x5_2<F>,
			PoseidonCRH_x5_2Gadget<F>,
			TreeConfig_x5<F>,
			LeafCRHGadget<F>,
			PoseidonCRH_x5_3Gadget<F>,
			TREE_DEPTH,
			INS,
			OUTS,
			M,
		>,
		Vec<F>,
		Utxos<F>,
	) {
		// Tree + set for proving input txos
		let (in_paths, in_indices, in_root_set, in_set_private_inputs) =
			self.setup_tree_and_set(&in_utxos.commitments);

		// Output leaves (txos)
		let out_utxos = self.new_utxos(out_chain_ids, out_amounts, rng);

		let ext_data = ExtData::new(
			recipient,
			relayer,
			ext_amount,
			fee,
			out_utxos.commitments[0].into_repr().to_bytes_le(),
			out_utxos.commitments[1].into_repr().to_bytes_le(),
		);
		let ext_data_hash = keccak_256(&ext_data.encode_abi());
		let ext_data_hash_f = F::from_le_bytes_mod_order(&ext_data_hash);
		// Arbitrary data
		let arbitrary_data = Self::setup_arbitrary_data(ext_data_hash_f);

		let circuit = self.setup_circuit(
			public_amount,
			arbitrary_data,
			in_utxos.clone(),
			in_indices,
			in_paths,
			in_set_private_inputs,
			in_root_set,
			out_utxos.clone(),
		);

		let public_inputs = Self::construct_public_inputs(
			in_utxos.leaf_publics[0].chain_id,
			public_amount,
			in_root_set.to_vec(),
			in_utxos.nullifiers,
			out_utxos.commitments.clone(),
			ext_data_hash_f,
		);

		(circuit, public_inputs, out_utxos)
	}

	// This function is used only for first transaction, when the tree is empty
	pub fn setup_circuit_with_data<R: RngCore>(
		self,
		public_amount: F,
		recipient: Vec<u8>,
		relayer: Vec<u8>,
		ext_amount: Vec<u8>,
		fee: Vec<u8>,
		in_chain_id: F,
		in_amounts: Vec<F>,
		out_chain_ids: Vec<F>,
		out_amounts: Vec<F>,
		rng: &mut R,
	) -> (
		VACircuit<
			F,
			PoseidonCRH_x5_2<F>,
			PoseidonCRH_x5_2Gadget<F>,
			TreeConfig_x5<F>,
			LeafCRHGadget<F>,
			PoseidonCRH_x5_3Gadget<F>,
			TREE_DEPTH,
			INS,
			OUTS,
			M,
		>,
		Vec<F>,
		Utxos<F>,
		Utxos<F>,
	) {
		// Making a vec of same chain ids to be passed into setup_leaves
		let in_chain_ids = vec![in_chain_id; in_amounts.len()];

		// Input leaves (txos)
		let in_utxos = self.new_utxos(in_chain_ids, in_amounts, rng);

		// Tree + set for proving input txos
		let (in_paths, in_indices, in_root_set, in_set_private_inputs) =
			self.setup_tree_and_set(&in_utxos.commitments);

		// Output leaves (txos)
		let out_utxos = self.new_utxos(out_chain_ids, out_amounts, rng);

		let ext_data = ExtData::new(
			recipient,
			relayer,
			ext_amount,
			fee,
			out_utxos.commitments[0].into_repr().to_bytes_le(),
			out_utxos.commitments[1].into_repr().to_bytes_le(),
		);

		let ext_data_hash = keccak_256(&ext_data.encode_abi());
		let ext_data_hash_f = F::from_le_bytes_mod_order(&ext_data_hash);
		// Arbitrary data
		let arbitrary_data = setup_vanchor_arbitrary_data(ext_data_hash_f);

		let circuit = self.setup_circuit(
			public_amount,
			arbitrary_data,
			in_utxos.clone(),
			in_indices,
			in_paths,
			in_set_private_inputs,
			in_root_set,
			out_utxos.clone(),
		);

		let public_inputs = Self::construct_public_inputs(
			in_utxos.leaf_publics[0].chain_id,
			public_amount,
			in_root_set.to_vec(),
			in_utxos.nullifiers.clone(),
			out_utxos.commitments.clone(),
			ext_data_hash_f,
		);

		(circuit, public_inputs, in_utxos, out_utxos)
	}

	pub fn setup_circuit(
		self,
		public_amount: F,
		arbitrary_data: VAnchorArbitraryData<F>,
		// Input transactions
		in_utxos: Utxos<F>,
		// Data related to tree
		in_indicies: Vec<F>,
		in_paths: Vec<Path<TreeConfig_x5<F>, TREE_DEPTH>>,
		in_set_private_inputs: Vec<SetPrivateInputs<F, M>>,
		in_root_set: [F; M],
		// Output transactions
		out_utxos: Utxos<F>,
	) -> VACircuit<
		F,
		PoseidonCRH_x5_2<F>,
		PoseidonCRH_x5_2Gadget<F>,
		TreeConfig_x5<F>,
		LeafCRHGadget<F>,
		PoseidonCRH_x5_3Gadget<F>,
		TREE_DEPTH,
		INS,
		OUTS,
		M,
	> {
		let out_pub_keys = out_utxos
			.keypairs
			.iter()
			.map(|x| x.public_key(&self.params2).unwrap())
			.collect();

		let circuit = VACircuit::<
			F,
			PoseidonCRH_x5_2<F>,
			PoseidonCRH_x5_2Gadget<F>,
			TreeConfig_x5<F>,
			LeafCRHGadget<F>,
			PoseidonCRH_x5_3Gadget<F>,
			TREE_DEPTH,
			INS,
			OUTS,
			M,
		>::new(
			public_amount,
			arbitrary_data,
			in_utxos.leaf_privates,
			in_utxos.keypairs,
			in_utxos.leaf_publics[0].clone(),
			in_set_private_inputs,
			in_root_set,
			self.params2,
			self.params4,
			self.params5,
			in_paths,
			in_indicies,
			in_utxos.nullifiers.clone(),
			out_utxos.commitments.clone(),
			out_utxos.leaf_privates,
			out_utxos.leaf_publics,
			out_pub_keys,
		);

		circuit
	}

	pub fn setup_keys<E: PairingEngine, R: RngCore + CryptoRng>(
		circuit: VACircuit<
			E::Fr,
			PoseidonCRH_x5_2<E::Fr>,
			PoseidonCRH_x5_2Gadget<E::Fr>,
			TreeConfig_x5<E::Fr>,
			LeafCRHGadget<E::Fr>,
			PoseidonCRH_x5_3Gadget<E::Fr>,
			TREE_DEPTH,
			INS,
			OUTS,
			M,
		>,
		rng: &mut R,
	) -> (Vec<u8>, Vec<u8>) {
		let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, rng).unwrap();

		let mut pk_bytes = Vec::new();
		let mut vk_bytes = Vec::new();
		pk.serialize(&mut pk_bytes).unwrap();
		vk.serialize(&mut vk_bytes).unwrap();
		(pk_bytes, vk_bytes)
	}

	pub fn prove<E: PairingEngine, R: RngCore + CryptoRng>(
		circuit: VACircuit<
			E::Fr,
			PoseidonCRH_x5_2<E::Fr>,
			PoseidonCRH_x5_2Gadget<E::Fr>,
			TreeConfig_x5<E::Fr>,
			LeafCRHGadget<E::Fr>,
			PoseidonCRH_x5_3Gadget<E::Fr>,
			TREE_DEPTH,
			INS,
			OUTS,
			M,
		>,
		pk_bytes: &[u8],
		rng: &mut R,
	) -> Vec<u8> {
		let pk = ProvingKey::<E>::deserialize(pk_bytes).unwrap();

		let proof = Groth16::prove(&pk, circuit, rng).unwrap();
		let mut proof_bytes = Vec::new();
		proof.serialize(&mut proof_bytes).unwrap();
		proof_bytes
	}

	pub fn verify<E: PairingEngine>(public_inputs: &Vec<E::Fr>, vk: &[u8], proof: &[u8]) -> bool {
		let vk = VerifyingKey::<E>::deserialize(vk).unwrap();
		let proof = Proof::<E>::deserialize(proof).unwrap();
		let ver_res = verify_groth16(&vk, &public_inputs, &proof);
		ver_res
	}

	pub fn setup_keypairs<R: RngCore>(
		n: usize,
		rng: &mut R,
	) -> Vec<Keypair<F, PoseidonCRH_x5_2<F>>> {
		let mut keypairs = Vec::new();
		for _ in 0..n {
			let priv_key = F::rand(rng);
			let keypair = Keypair::<_, PoseidonCRH_x5_2<F>>::new(priv_key);
			keypairs.push(keypair);
		}
		keypairs
	}

	pub fn setup_leaves<R: RngCore>(
		&self,
		chain_ids: &Vec<F>,
		amounts: &Vec<F>,
		keypairs: &Vec<Keypair<F, PoseidonCRH_x5_2<F>>>,
		rng: &mut R,
	) -> (
		Vec<F>,
		Vec<F>,
		Vec<LeafPrivateInput<F>>,
		Vec<LeafPublicInput<F>>,
	) {
		let num_inputs = amounts.len();

		let mut leaves = Vec::new();
		let mut nullifiers = Vec::new();
		let mut private_inputs = Vec::new();
		let mut public_inputs = Vec::new();

		for i in 0..num_inputs {
			let chain_id = F::from(chain_ids[i]);
			let amount = F::from(amounts[i]);
			let blinding = F::rand(rng);
			let index = F::from(i as u64);

			let private_input = LeafPrivateInput::<F>::new(amount, blinding);
			let public_input = LeafPublicInput::<F>::new(chain_id);

			let pub_key = keypairs[i].public_key(&self.params2).unwrap();

			let leaf = Leaf::<F, PoseidonCRH_x5_4<F>>::create_leaf(
				&private_input,
				&public_input,
				&pub_key,
				&self.params5,
			)
			.unwrap();

			let signature = keypairs[i].signature(&leaf, &index, &self.params4).unwrap();

			let nullfier = Leaf::<F, PoseidonCRH_x5_4<F>>::create_nullifier(
				&signature,
				&leaf,
				&self.params4,
				&index,
			)
			.unwrap();

			leaves.push(leaf);
			nullifiers.push(nullfier);
			private_inputs.push(private_input);
			public_inputs.push(public_input);
		}

		(leaves, nullifiers, private_inputs, public_inputs)
	}

	pub fn setup_tree(
		&self,
		leaves: &Vec<F>,
	) -> (Vec<Path<TreeConfig_x5<F>, TREE_DEPTH>>, Vec<F>, F) {
		let inner_params = Rc::new(self.params3.clone());
		let tree = Tree_x5::new_sequential(inner_params, Rc::new(()), &leaves).unwrap();
		let root = tree.root();

		let num_leaves = leaves.len();

		let mut paths = Vec::new();
		let mut indices = Vec::new();
		for i in 0..num_leaves {
			let path = tree.generate_membership_proof::<TREE_DEPTH>(i as u64);
			let index = path.get_index(&root, &leaves[i]).unwrap();
			paths.push(path);
			indices.push(index);
		}

		(paths, indices, root.inner())
	}

	pub fn setup_root_set(root: F) -> ([F; M], Vec<SetPrivateInputs<F, M>>) {
		let root_set = [root.clone(); M];

		let mut set_private_inputs = Vec::new();
		for _ in 0..M {
			let set_private_input = SetMembership::generate_secrets(&root, &root_set).unwrap();
			set_private_inputs.push(set_private_input);
		}

		(root_set, set_private_inputs)
	}

	pub fn setup_tree_and_set(
		&self,
		leaves: &Vec<F>,
	) -> (
		Vec<Path<TreeConfig_x5<F>, TREE_DEPTH>>,
		Vec<F>,
		[F; M],
		Vec<SetPrivateInputs<F, M>>,
	) {
		let (paths, indices, root) = self.setup_tree(&leaves);
		let (root_set, set_private_inputs) = Self::setup_root_set(root);
		(paths, indices, root_set, set_private_inputs)
	}

	pub fn construct_public_inputs(
		chain_id: F,
		public_amount: F,
		roots: Vec<F>,
		nullifiers: Vec<F>,
		commitments: Vec<F>,
		ext_data_hash: F,
	) -> Vec<F> {
		let mut public_inputs = vec![public_amount, ext_data_hash];
		public_inputs.extend(nullifiers);
		public_inputs.extend(commitments);
		public_inputs.push(chain_id);
		public_inputs.extend(roots);

		public_inputs
	}

	pub fn deconstruct_public_inputs(
		public_inputs: &Vec<F>,
	) -> (
		F,      // Chain Id
		F,      // Public amount
		Vec<F>, // Roots
		Vec<F>, // Input tx Nullifiers
		Vec<F>, // Output tx commitments
		F,      // External data hash
	) {
		let public_amount = public_inputs[0];
		let ext_data_hash = public_inputs[1];
		let nullifiers = public_inputs[2..4].to_vec();
		let commitments = public_inputs[4..6].to_vec();
		let chain_id = public_inputs[6];
		let root_set = public_inputs[7..9].to_vec();
		(
			chain_id,
			public_amount,
			root_set,
			nullifiers,
			commitments,
			ext_data_hash,
		)
	}

	pub fn setup_arbitrary_data(ext_data: F) -> VAnchorArbitraryData<F> {
		VAnchorArbitraryData::new(ext_data)
	}
}

// const TREE_DEPTH: usize = 30;
// const M: usize = 2;
// const INS: usize = 2;
// const OUTS: usize = 2;
pub type VAnchorProverBn2542x2 = VAnchorProverSetup<Bn254Fr, 30, 2, 2, 2>;

// For backwards compatability
// TODO: remove later
pub fn setup_vanchor_arbitrary_data<F: PrimeField>(ext_data: F) -> VAnchorArbitraryData<F> {
	VAnchorArbitraryData::new(ext_data)
}
