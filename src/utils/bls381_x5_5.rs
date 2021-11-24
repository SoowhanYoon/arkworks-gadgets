// https://github.com/webb-tools/bulletproof-gadgets/tree/main/src/crypto_constants/data/poseidon

// Parameter for:
// exponentiation = 5
// width = 5
// full rounds = 8
// partial rounds = 60
// prime field =
// 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

// Sage script command:
// sage generate_parameters_grain.sage 1 0 255 5 8 60
// 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
use crate::poseidon::sbox::PoseidonSbox;

pub const FULL_ROUNDS: u8 = 8;
pub const PARTIAL_ROUNDS: u8 = 60;
pub const WIDTH: u8 = 5;
pub const SBOX: PoseidonSbox = PoseidonSbox::Exponentiation(5);

use ark_ff::PrimeField;
use crate::utils::parse_vec;
use super::parse_matrix;
#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_rounds_poseidon_bls381_x5_5<F: PrimeField>() -> Vec<F> {
	parse_vec(ROUND_CONSTS.to_vec())
}
#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_mds_poseidon_bls381_x5_5<F: PrimeField>() -> Vec<Vec<F>> {
	parse_matrix(
		MDS_ENTRIES
			.iter()
			.map(|x| x.to_vec())
			.collect::<Vec<_>>(),
	)
}

#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_full_rounds_poseidon_bls381_x5_5<F: PrimeField>() -> u8 {
	FULL_ROUNDS
}
#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_partial_rounds_poseidon_bls381_x5_5<F: PrimeField>() -> u8 {
	PARTIAL_ROUNDS
}

#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_width_poseidon_bls381_x5_5<F: PrimeField>() -> u8 {
	WIDTH
}

#[cfg(feature = "poseidon_bls381_x5_5")]
pub fn get_sbox_poseidon_bls381_x5_5<F: PrimeField>() -> PoseidonSbox {
	SBOX
}

pub const ROUND_CONSTS: [&str; 340] = [
	"0x5ee52b2f39e240a4006e97a15a7609dce42fa9aa510d11586a56db98fa925158",
	"0x3e92829ce321755f769c6fd0d51e98262d7747ad553b028dbbe98b5274b9c8e1",
	"0x7067b2b9b65af0519cef530217d4563543852399c2af1557fcd9eb325b5365e4",
	"0x725e66aa00e406f247f00002487d092328c526f2f5a3c456004a71cea83845d5",
	"0x72bf92303a9d433709d29979a296d98f147e8e7b8ed0cb452bd9f9508f6e4711",
	"0x3d7e5deccc6eb706c315ff02070232127dbe99bc6a4d1b23e967d35205b87694",
	"0x13558f81fbc15c2793cc349a059d752c712783727e1443c74098cd66fa12b78b",
	"0x686f2c6d24dfb9cddbbf717708ca6e04a70f0e077766a39d5bc5de5155e6fcb2",
	"0x582bc59317a001ed75ffe1c225901d67d8d3764a70eb254f810afc895cbf231b",
	"0x076df166a42eae40f6df9e5908a54f69a77f4c507ea6dd07d671682cbc1a9534",
	"0x531f360b9640e565d580688ee5d09e2635997037e87129303bf8297459ab2492",
	"0x30be41b5a9d8af19a5f922794008a263a121837bcbe113d59621ea30beefd075",
	"0x39f57e4c8a1178d875210f820977f7fcd33812d444f88e471040676e3e591306",
	"0x3514084b13bc0be636482204d9cddb072ee674c5cb1238890ee6206a3e7bf035",
	"0x6372b6bc660daf6b04361caff785b46bbe59eb6a34ab93e23d6364e655dc3a36",
	"0x422af985e648814bec5af62c142828e002d4b014b702760106b0b90c50d11de5",
	"0x3296e51f12e0f5c49747c1beb050ff320e2eb7422807eb0c157a372dba2ea013",
	"0x3b76246abaf33b03dd5b589b80a7fac0ae7f1ad8a9623bb7cf7432c90e27358d",
	"0x0b40e7e02f5cb836c883c7cef72ec48e87c1808f7d829e2ee0bec0ee709f7409",
	"0x2ee81b5c29c93b8a6e8871c01d0380a698e547475359b4a4befc22ed2232690f",
	"0x341ff90fc4a8afee9b74c464955ba9b357252e915b8d39ea7c1318eda718f54d",
	"0x55eddabde058f3b5e9dae90873ec9bd7b05927da36925e7dfb7bc290c1da125e",
	"0x6b34ad8cec56aae4595c403377cd2aa990a2f09b931f832781221965bb081b1c",
	"0x707de76df294fb845309d2160e1bdffebefd57a80c8658899e2c95e77254c752",
	"0x05e9b152bfd4946b9c109f930eb01892f314597507d28c735a266f4277bb2a32",
	"0x1589a5cbcee13b696b6f0a1dbbabc08394ab00ed5a6ae6435020e9e3e2fc909a",
	"0x7116a5d027fe73fbc45bfc60fd875c3116fe3a567e830d1d2d38655223dbd7ec",
	"0x05382ee6ad97381eb3137f5a90ea13298dac6bc7c2204906044fafc01bfe6ae4",
	"0x0900bcfe5e7c1b7d0aa80c714b7b2a0c1df7473362138a9dc5c552d11c1d0015",
	"0x0513deb89d2e48fc729440dc08d0256a79cda84d511a04e0d92cce3c7e55a7c2",
	"0x6bbb5f1736d499fe3fda42ad40a2b124952ac35fe970ebde38c65cc20ad2afc8",
	"0x5782ac68a8da0ba09f4d17e7e4b46caa4411a27e60be92168ce75bed95453e05",
	"0x2d83f3324639c5d83a1ffcf6ac693eef98d8ea4877d547c62b304b0a9f4a0c28",
	"0x16d3a13700ec503e29ca4d0c6342864595134408b6668bbf1766bb48d7f96cba",
	"0x318050e971e075931253b00430d35f89f40a88fc73d62150882a8e87149d7244",
	"0x7180760dd839d8bffbf9b1e26826cb4f6de65fa868a8143e1dc8c2b6ac6d1ac2",
	"0x5cf2aa95907e59c4725cc17c8cf492f9a7eeef2de337ac227a983c444ae0e80e",
	"0x2b8345763484d7ec02d6ee267b7c737ca9de41e2186416bf91c65eb0cd11c0a4",
	"0x055aa90aa60ef9b7f3c29c7500c64e6b85929220a6418dfad37ead3928059117",
	"0x541d5e4be0967bf49a595c1d8290b750305a334f3347c01b57f8ba313170e1ca",
	"0x05c0a1f16f97f582caaf4338f018f869e8dd0fa32f007bad1a1a4780053d5817",
	"0x01519e13858591aa93b9c1d7f849276ac1d2011b7fd19a475371c7968d9f52cd",
	"0x69c30d5a27f4dffa19c956c348287a704676d999f23044036b9e687a45a1a113",
	"0x58c93b899aa53e06e82b6346e36338841ba7279d2b7a0ecd3aa20f292852936f",
	"0x06b8a12870a15479d41018fed6f1a29102ae23e13d0fbccec93ace48bdb9dc93",
	"0x33eda3c347379e61c2297aa1026682d22f95dc3c7e46e68ab3adb4b0939d76e2",
	"0x187728045111275b93a1218a148ada85a1f6e2059c443ac7d61fe81e3130b89b",
	"0x397ec485c5a8b0c8a03ff543e9a9e5a4dc0dd4849fe955bb77b452e2e22c4f17",
	"0x2f33f8de90f81248455d5a6592667092992be0468372addbaff664caa84cd2d5",
	"0x061a1a458994ddf9f38c5edfbd737d3ceb05deaee685058b14943e7e9246ebca",
	"0x4b73ab5b9d35f47307b731e3cf1a1a22e7068e2744f2af0ef6bd78bf8aae4845",
	"0x5578b7ad5f8d4f3b8e618af7d8d5ec8bf837d2d9486527fe2f9bf7464f8516ad",
	"0x50b4f055d860f89e12883209f847a4b1a2395fb419eb53c182dbb555c962255c",
	"0x0b2da770936d6c778be289557ddd2ca024b93fa38c5d4541344e883a69611813",
	"0x47d8441e1ae7cb8ffc52a18c67afff3cf7543cad51605b2d4e2513f1e1868b68",
	"0x619da3bf44b42acd949ed572c9f3c195ed20b0b91bcd9e95ee3750d26f3b0ebd",
	"0x6c9e249e89b2b4cf9cd7772950e0cc9d06688d4f051095eafd116371ede49ab7",
	"0x210bd3217a141c55877d4528a4e80d5d81d78de7addce85994082281a6250d4b",
	"0x4e1d8e4079c14c83847af6394d7dc23f33ebf71593379583ec574bf5c86ea9a6",
	"0x699187330fc1d606e8b31b677651a2c7d1c87d4d001018031792cad0ad3f2826",
	"0x2946bfc0f45c1f1a0dc4c343a85259f6a6237f064481fe66eda76f01998a01ea",
	"0x5543e07588375c6d800e5e42d1bfd8b7a92a2a35d65b234ded85f879f82a3d66",
	"0x660e9d0f2f866e8d12b40dd9d9c03cc8b9ca78600bd649f0fffb2c388dcc8b43",
	"0x38f06c48d4dc53cb1b69619244cc2a610fdc4229ea316980dffe9131a72b4209",
	"0x5c9a73a16521ddf463f9de314dd5f7255bc66add48297615b761f34e4636762d",
	"0x310931f0204c9936fe659e9ebbda832c930172130b3f5476c6c6ee5e7fef3e45",
	"0x72eb1d833664d8989998af11441ac49654c12210b3465e5ac67a99679634a3af",
	"0x6981346585a2a466a9255841f710e1d083bdcc21c0aa6721745e158218767a94",
	"0x0370a259836b3766d563ed3cdcf55ace52655111a1017d8c76eaf8f97e81d858",
	"0x4f63c45a324b8b974c22a20a6c670eb62d47ef900541b63f1d362b8bbe4ec418",
	"0x6a4c7347121c2d4745ecffaad22281cc4d58ea74453b7d2b625b890190fdc7ad",
	"0x36d8869bb69a51ee99622af09d6878c5b715084b25f6e4560a7498557fe87fb5",
	"0x18faa7f51e1b7a442f9123806872094c0de8a46a6d8402f31f0cde3fcb878394",
	"0x3610d022aacbe58593e0d6aa7eefdca767f5ddfe7fa1fb9fb4f80225d82b617b",
	"0x3b5f13d6a8bbff31569bc6860087b2a4b361146a04ad5fc7396a3d0c59f68c1c",
	"0x40e919335051c6aaaee033745c41b6fa36739a097d94ce6eb075ec03da2a978b",
	"0x2f54586ab9b7886340f8ed5254f29128a85e2fb1e3725bf3c9cd8bddadc947f1",
	"0x00606231b689a040363e5afc050f9fc9296d6c620a885eeaffe91be387cbe96c",
	"0x4b55696db6b0fa327527a76e6ab6b688561c879e53d858e4c90a1122210130e1",
	"0x569c39bd78356991953aef4b1a01fdf71710bb05eea1f447c3e5efe13bd62894",
	"0x537f73fcaa256497a2582e45105f1dc10f39c7fce9b88cab5523af3f5f82dcd9",
	"0x2d58d32120c25995cd0754ab9fdf9ad67d67623cfd1fcbf489f51fa6e6eee4a2",
	"0x37cb0f655951fca18a4ccdddd4d8466f8839ba8e320a104cb47a59cd387d322f",
	"0x4e29d154430c9bced788d2eed8f3e01b5da24c1d3710e490bc40ee6d5903213c",
	"0x47597b7a9018192ef22d6dd24555af1c0c51d8a90b54d8a0bdc2df7967d7a28b",
	"0x4e01b43205fca0b4a32582abe600f3a326035fe7e028cb0569bac43c997b98ce",
	"0x0172ffdfba7e43ca807d5b5de7727b4e41706c1f2858c1e8a46c27ed3eae5ff2",
	"0x2216dd907ab98c0d1e720a46ef83334a236d2c134ccf35ef8e889421e70ebe03",
	"0x168709f668b635f03607a39390a0de71306d6430ce2babf7292d789d25c0f8d5",
	"0x0ff6a3823440877dfd355dea80595e21115d0dfe3472cec4ad1437572cc6151d",
	"0x44e37699b3c72f50ec1a754c72e6fa3f5a074181dd63d189ba36447d34e536ff",
	"0x267298d2e46227f7f7f422e3059f18d83a8795731b13f6568ce54730cd3fe9ae",
	"0x1ecbe7a60848077203373441a5b09b44693a155fe226442259e37ac47209235a",
	"0x31cb23e6b5d7393577d5f5c3368c5bdd5b434ee6319f07e502031cc393d4eccb",
	"0x5d4c550c4a6eccd74b74d6279b3d9bc755084588156a1bef673657dc2116ecfc",
	"0x226056b5dec9afd19190ac48740c3b5ab1bb429b19f56894a3dec3f104d238c0",
	"0x09077c021183dd37ad10451ded70d7ae6ec4819ae76ce23fb2a0be63e69907d9",
	"0x53545c868ba0fbf0ed1ed7a24ec11b2ecfba5b37fd5cee80774e1ecdea991ed4",
	"0x69521c33d148e678ca10b33103812cd27597c4a6cddbe83f4970d4b96e03304d",
	"0x01d5779be7477b96aac6532ef919e61c624072be54587e0698999dd5f460e446",
	"0x57875a44441d2f191ac7d8de42691ab55fd3401bbaf04b786ef0603b3edf2927",
	"0x1d5c957da0832d5b94e76f7abdb190972774b594ed232810bfcafe5441839d37",
	"0x1b678335a80fd045fc7ce1897aa129f67bd55ca9ca801bd88eb7cc868538bd7a",
	"0x31e69d706a5c1e011c1cb1809e5bf1857c90f9f50b9e1ae5ad36e4d3dcdbb7ed",
	"0x485df8462ed7a18de34aa6e99ecc9bbf2db075a096b56bc2943b76a99c4bb1a0",
	"0x1e46fdcbb3705f663a350e78f99024912d80c95779195807aae82cbb494ce9e4",
	"0x441d0fa0e9cb86c3a2a1f87151681c603c3e028f1a0670be2149eed4f0a24f08",
	"0x02a3caff274f40942062340ec1fae17c1b1e97c2f0fc7e847c90e9317fea2c0c",
	"0x4caf281080c0b2f2f638bf0f4859442f4c9da94e9994dada34c5c914130c1a9e",
	"0x444470c6c49b5b9a38181c3af20bcfea572450946135baea85cfd6b692fa6464",
	"0x6d5e07a13376fc883bea2dcdbad7f80b7780f231cdd33f5b98618f42cc49ec2f",
	"0x1b9470418a07d8c88c767d1e63e8d5cc7f810cc530db1340181ecbbb212e0f70",
	"0x4134c8666c685b712f4aec72077c540ef4a041dcaa123caabd57b83fc6266f14",
	"0x3d5d0489e27362db9bf0cc7217477d81d2a73e1a44edc43e32d43bb544287c9d",
	"0x71d7d4a91945e796f538f03b9324497489009ec1a0a403de062ed5bb4d7c2400",
	"0x646c3d732a94f722384ac266b41e06cf21bf24fb9426c9556d8ac9514f0875f7",
	"0x4f860c9e5d9bb73057d93c207902d9e60fd6a7c779fde1ebf16b853dba1ea9ad",
	"0x05801566eb9e119e2f9ace565c9488cd999d66a5753eb4b9887363137baa09ab",
	"0x0263bdb8654cf1245ae4589370dfd5eeb109a50944eef54308566055b887ee01",
	"0x4cc39561e65eb05cb8c83f9854750a9114a996eb23e6a0bb07d2d61f0baf0a62",
	"0x36b544778b2fdb94f808ad8d077b7f0b44f3bba515ecdf026919e2fed09a106d",
	"0x3fb1f7aec47cbe990151d4bf703c38349b95f409abdf0504e67c1a55ef82294c",
	"0x637e7eb19cf539aada7e48bc6b72e5ccb0e3f6913f18a0d55696dddfcb1b587a",
	"0x73bc630fcece6947fb81ac8e0f1f1671ed6042c3ef3bbb12ed554f28b48b46ec",
	"0x304b46f52d597b964fbec3fc0dceee442febe6131359e156c194ab7be2a11e6d",
	"0x067d85956dcfff7fd9f6a0fec505b7f4998e3d85672623677a6d974d6b111de6",
	"0x65830d8053bf8afc0ba5274f1a4c4cce617fa624b480f13ed3eb369fbba78e67",
	"0x6c32c101e08a962bd996d759a6c012a4d97aedaab9fc99c1fa735a16cd24dd44",
	"0x11fb2d160e41a1845fd14578c617285081fb1a16a21b36cfd5065b30fac574e3",
	"0x50aada39348c4736f6c59f7f053c488ed999a33ad23501d9c635aa03baf90db5",
	"0x5a5f0e3a32b260fbdfdc8c0eaf3a99396992b50b6dbb63a9d1e1ddf9c91d78d4",
	"0x62c9f6d9aea355d358f2986ad487c2ae443122e1edfb076930865608d05c3b39",
	"0x520cea06cee20150703a1c8000d4a5f22b3efeb9e34eb90bad0b4ff091b33683",
	"0x6da4e4682545c1f4c0076f5845fbbcf48632a9c193a92593d12d248031f2c893",
	"0x1ba5502cee2ea2d07a64f68f0a7492d2426382a5b9662d0410e086107399989b",
	"0x6ab843ca92240f8a82862da071d53f048272d55425907fc8d0e60dcccd5a1ea4",
	"0x3f65c2dfa6bb39c1b291c40f810cc912015384a2a24fd322b6375e27bd069322",
	"0x6a2df71a64cb0d9a548e3b65ba4e646ff5e519cab564b5f77b3fe08e038b9c3a",
	"0x64776bf2b66bcd09c8661ee6ca6b8251bb4aba5a7ba181464d905db561ca45e1",
	"0x6d7bed0d258b518eda13368f00be2cc0a94d71cc203d5905c35b10a3ee53eea8",
	"0x371b958b5c79c889d1786edfe404119773f728822637fb4890b8847a93f97af1",
	"0x56923182c33cb4dbf0988ba2314378dfd7491b3467b6134e6283c87a1478cbb8",
	"0x3c4304994ef664d6aa19e3db492c306534281b5b6f857fa6ffae67bdba99c09e",
	"0x0d003bd3068fa94c4f7bbe6ba02993acd341a27ed2fd7ecaa4e6b0b9d0abd85a",
	"0x1073cb8c08510e7d88ed4cdf78e96b297cabe9d6677db47289b056c2a640da01",
	"0x5c57522580fbc75883658d4b7b8ea07e1a4fc75f453c09edd9d249ff1bd31ae0",
	"0x2a5bec9b422b4dc64958f4752d0c091ffa7904e0ce4809728d16235bb41d707f",
	"0x379c4a9b4174c5878f72b60fa985f7aa86c1fd868683bdbe8fae194cda2e56c7",
	"0x3634e042e79d046adb911d57b338e78f51ac7d212c5a5c6dc4fa1a05ddb58c82",
	"0x3ace976310c5040e1484d1a6d42993ac5923d474ce5497a3fac468af25843a01",
	"0x3f5a856ab863b7584bc2e6e4c610b9df55a9306eb68894d630ff7d04f243e6f5",
	"0x0d52822f5581fe9c5dab0b1f8d04eae183deb87c89504544a3d5558594b3149b",
	"0x3c119e173586c22059bb09d2af4fc1044c8fc44f709233f7625e5fffa6696596",
	"0x3e154fd5a026d7c6584faf8c089d82fd560f138392a8d4a5fe287859994c96b5",
	"0x47251339c44d737b21df0ed1e204a28b68c9abb58f1cf2232f8a2da433e24b0b",
	"0x73d84625f38db2f3842d7724d8e79d6d0349a93b8d6142603eea382ba6ed8692",
	"0x42929bffc19bf9cd1c53d10440b0760a3be6442db20458b692b4ba3901e6003f",
	"0x39b16b0fc3700aa93e0cac53fcaf7e84495ac3b49553b2e1a5ff9f73fe74de50",
	"0x2b715e21640cfb6f77b91a4f6d3dcaef9b5faa7c0bfe94c8d80b0824292603bc",
	"0x306bef0c637b5d7c8d6486915f6623f4e1ed81971f40772ec60feb5e243d32a0",
	"0x5287d6ece65ef5df6e1c65dddf1d97cfa019157a5c90c004527c9d7c7496d814",
	"0x0d760a2132c9092b0c8c89cbdf4fb1bd282791ef6284b73a44b313e8118e7d0c",
	"0x5e830f4484268a349e4d9f6178ef745460f1f8456b04d0dc7814844052d51eb5",
	"0x2468669481610965d8439f60a66aa61fbc7b18e82b35aa4755873ec4db82174e",
	"0x23b6ea9e4d1fde701c719c2afab1272ea22b172bf7afe0837364ad9a2f698bd4",
	"0x412024b2e86e9d5e903a5fbda26200be47003e3b0dcc322480d3079850606cc0",
	"0x1f64c17825c1ce9333d211d45a555b5ceaa4608a354ed3237db56225b3a9459b",
	"0x0b66fa87587ab95d5d29dde50cd606a1bc2c45fd223c03d0693c88b13ae23039",
	"0x3086c386026698e733e54e5e17f65cb26c17fe64e76f85902cc184d5dd8ef0cf",
	"0x72036acd9ef575414d5437327d902da6396cc70c0bcffcef2a82b4c296b5ea93",
	"0x53d89e4470b3ea1eb861717e47c08fda42f6e61fc08118b16645ae5e8fdd664f",
	"0x4ebea65d1fc5c5167b1412ffcbf8900a8df2096c25d7011e6c74f500662465f8",
	"0x5ee6e1e0312e78e2e67b246a95afdd79e2e7a5b9b0ef6ee36c3d1639f9736e65",
	"0x1d770c0cc2c2231213624d58b7875b1715554f6100784bb2b545e405c7fcb94e",
	"0x2ea5c9837af445988c480fc6a55b1e5640dbe38d5e8cf1ddd85bc42c3658d9ca",
	"0x6fb78d12c35235f738b1667749064d0066fa7cfe3a9624cb0944f16d37bc485e",
	"0x35b75e89e794282cee1e66991ccfb2499dce4366b88d7be5f7b5775c12103a22",
	"0x50e83b08162e7ccfe2d0f19aea4753ba83ef5c40572d6e904cfe2419ee9d901d",
	"0x3fc5c93031cbcecf12d5831aaa6b2b3071657cd669f7b377b2fef4a7bfc9adf2",
	"0x37895bdfe29a174b98cd4b49104e56ea09e41c7b50f9aa95b400b529c545f5b4",
	"0x695e405509a0981035ba77e27cdcf53f3bc15d20fe4e43a335aeb6406ae1837d",
	"0x104985a48aa7e0a668d8cc7140c255ed1b8482ac5febbd3d7a1cca0e96cf0682",
	"0x118220b30330f1954e7d94d40fb1043a1a79ca83e68e9ef590601a86a4a917a4",
	"0x098b3be7845a63543c13d211efac076b94a9528d34cb355faf0ff7a0d5ee9991",
	"0x69ca1313dcddd8c2f5c5c7ee93a1d2a94726c0c0bc4a303fcf83109b23bf3621",
	"0x570c1bd286b258b8bf11e8b85a2eb0c6dbfc2e4cdf01a0cde5464aa009b5bd43",
	"0x4f2921de3696018e0d1ca7cdd5a4064ebf51845ab25b2d395b71c341ea8527da",
	"0x19035c69cbaf0e0e7e02c5c524a8cc56de0e52d1936a9a10b7580f0c0555878f",
	"0x2b8fdad2064a6f58d01e8c48d49bb25730780055829c1faead0430afcfbc5669",
	"0x60ef9a74bbf8b98cb8248856492257f30c7520b3353a6fec9d90d48be46070ba",
	"0x4c9a6bc8284e783afd6c425f8cbdab82c0db3eac060a2dc00eca48ed6d1d052b",
	"0x68e6d3a83ac8e60c92d2860ff7557e1fbe3b91c38fabbde8b28371dccce2a10b",
	"0x56e0e39848046f0305d268b28aa753a41d48586e8579d5f95f12dba60e181d4c",
	"0x5176824fd8c92fed23df24c382a9fdf86aeeecab0b6716bef53da57bd3f551eb",
	"0x3aaf796b71041e8b2b494bca3b030f56a0c5663149093c8a179c0f3e24d0f718",
	"0x101cd65865abc573f5382df3636f4d60bc669aaa70f09ba040d61ef8d09c5296",
	"0x2581f83d616d932b438bfe0062082d4e1ed7d34b9a1cf63580199731d44a4b25",
	"0x65d74f6d1320dd1dc9412547b130bc7ad03c4e80cd8a44c108f24ec7aa35489a",
	"0x0d5cb6e19c9aac7d9f51f176ed42d008317a189dc4f6fc5c36fc6d451a035916",
	"0x0e367d17423501e62db9fd487f72076f2d1de6dabd3c175341ce35f925c9941e",
	"0x3f3f101f7c8abd6bebe6b81dadf0ff5fa31ec7140e317909a8d2f94ce4adc890",
	"0x6d5f212b5f4775095ab1d20fffd41dd73ab69b4ac60e9de11693f8e6bab88e67",
	"0x6b11154212e86e185a4cb17dc2b9dc061f72bf9cc3df5f95f7b87f1101d09f1c",
	"0x43f4cf980ff1a9101ca3c4601814f8de4124d108be2584ee9ffb9505188d35fd",
	"0x5d9be9303e3a25e8fa1abb6f2a7e3250231091100f9d7311b050b52666ec8f02",
	"0x1eb3b147885e1261d9034ca89a658817caef5ae629e1265cd32c6ef89ce704e9",
	"0x1595d95dac2c4653d32b01c3fbc294b2922140e41b93c5e7f5702212226d7140",
	"0x578b22f1f6d6eeb61507f0de1c817bb876b9cd079a18be9e99e2faa8e02618e2",
	"0x4de38f88c5e8ba1890b3695c912ccacd63721298c9ba3d3668b44f2a13b40abd",
	"0x0b9df0b81af072be21be9f08df336d3babe6ed5bfc199c73f2e97ccc73de80ae",
	"0x2a1a8c6d54abda22954e90386d40cc7d5c4f54c592ec2c69a9574601e88b6559",
	"0x5c5d96136cd1c4ae8fa1db9273083567345b407eb66f73a313ab8ad1a76cb157",
	"0x1ade9e2b734e937fc2fa04ca445236faf24e6d47ad1a4baa3408102c0d1e6363",
	"0x49354c394824998704e44eeb2ba6cb6fb431c334b648e6c87565e5fe133e8079",
	"0x4ea258f019a8055902a696b85547652519b8d8d92de4bf18e2dbfa41264a9a6e",
	"0x008a5162adf5ebd8711fd8139418509e472abc02908084f2e494086232336808",
	"0x6badee92872dcc00812a1cbc8081dd65ece0c7d3512af5a9df5fed7428557c81",
	"0x324c64ef2693e966965246bb7bb8c04b57a21fbee9be8c4a10096222bc83cc51",
	"0x3f14138eee87c93b0fbfe7efdcfa906525b0ce0f3b9a7431a492f8cb71514219",
	"0x0db99fa5ce25d50f557415ad181f1399840574f678b2534cae8f774bc8703009",
	"0x23d984702589f3275211041a4bde9d79329967723ec029da095bdbe733e97381",
	"0x6c5144ace155e976e287f1b95951194895bac2e5d54b07b62c3afe0eeafcbe39",
	"0x57a3e420fe7e0638bfb4d0b2c6286c2946166a6eb17836571909da153c3204de",
	"0x156621c4691a9240863577f10e29dc66a37d1b94e756869984c22d9f9d284726",
	"0x1b1e774a7ec903650adffe34f6aa8201d356e41e0951d38fb83a89413d078e4b",
	"0x514b940e5717c1ae53ea29b9a5a15998e294f69c1f553fe56124f66a16a78d53",
	"0x16350c6898d04d355d966c1d7827eee076a1ebd90781639e120feab665391ea9",
	"0x5b8b30d8c5ae46c4171d40478886c71c28fc86a3ae4a52ad1c05d8bcb9991b52",
	"0x5226cdc8a40c229ea4fb08f2c10e0e24cd41f24ca5fa5b5ab73e7340f632e727",
	"0x64383db664537c84a0a4030c3318f2f19cbeda46c70460035ad9d9240011639d",
	"0x61068a086ab73c87701b2642af25f6a430240936ba473a9a258cbf90db275277",
	"0x5bf320a3e8a48c6a85e2dffc4740d1b381ec4aa0771d885dc16adee569403ad3",
	"0x2603e0fd03264a856c1a7b8f1c5a22c3b98f4858c345e8e0a68e3f6424dd2dfb",
	"0x100d221342e64ed7e4f1520be70f5b0134031f8a31b4790ebb8e0a89e50b42e2",
	"0x0e61bad85ce909438ecc028b55085ec2cee0dd3ac5a7bcaa79d96186747a4606",
	"0x570a2045ca0fa7288d7f372f36bd075c2517a9743c9baa46503c4396e1f316f4",
	"0x1a64e108621e134020ea761d8f2c5bb42f24fab7641b095f1d164d1fc7b8be90",
	"0x097f0f28fd299e3597ffd761e9ae8b0fa46526c9d78503dc9dd5f61df3a085d7",
	"0x1d1063cb1be0f9f96aca5e5e39be9df69c96ff717c7d0c7cfe179cd6dce27505",
	"0x3e30f5d48b3c2475b8f3ba08cba27caed32b1cf67f76ba9223803733e13ad863",
	"0x2b30db4198cd832506017fa26430d204476113cc791ee110cf5586af5ce3824c",
	"0x2b520e374519be203c022ec51dcf8d972dd01abfaea371de9b1532647fca7bfd",
	"0x183b9a8e45fd480e822f8a97a8d2f127d0ef561914903229fbc5602bea46cb37",
	"0x4e01e6edf11ef4c94fe8589f9622a70709330a12e68591f6ea7dda994117bdc8",
	"0x52ee256fb3031d20fc299de7fabd0d4ef2e7f12539760dafb0fbc8560a40ee16",
	"0x327f5e141e4758d3d9a94c1628a57c817cf84fc0082b8dc098adbe84c1430979",
	"0x3d0e12036899e5be167de13913901831a714ea5617b94de6de070ddc117bac71",
	"0x1d9466d50efd1be3080d0aec4b81dd5cdf1ad4681e3ac04d08057f8fe49cdf0b",
	"0x2360abd7728da2dcda3f495a9a4f0f2aaff1d2420b8f6a7fed6592e1463f3d00",
	"0x23c1df4ddd6da863a1a2837e5222150278adfd4faf2fae7beaf64ed67a30736c",
	"0x1e98ec3b325a2a11738273f94516a9d56107f33062661e571342bc043764cf77",
	"0x431de5d108f8f7109df3059abcc16ccbd17e18676ef64f8998498e4a3f331fde",
	"0x550937f2bf0f1adb53f412d49ffd2886158703c375f87d059461f740d655e3d0",
	"0x1341fa99aca4bfc0f511dc9a9bc57c1e7aeb41ebb3a9140f5f93af1b3aeeb582",
	"0x706889448219016f970b32463a87e355b55ce0a34401dbfe4dd19fb3f93dec2e",
	"0x28d6207e409ab1c6e8e196d9e363040070b6c6fc4685a5482f80ba38cb792dc5",
	"0x6827087ecdf4e6bc7c396c59de859cbf08f92c361b5174e7f681ba0e72f83aaa",
	"0x553e112dab620286f6cf2d31325b971a6516dc7776a6e5ef37bcb11d1785299d",
	"0x40b44f7413d152f0d46460c54e9572fd91174b4b94a3595d709119e49925354c",
	"0x4d324dd7dfdf2380ef9f6d3c4f4bc4c5f90dbbbf2f1fd923256913f33a45cc09",
	"0x609b3ae79dcdc8a8379a690394c95805d862bc31068b572ac126bbc082ebf8b7",
	"0x33973520a1d9fb67048d64a22ad1b75b081d88c135a556dbc1b6a8479f75eaa7",
	"0x3bcb7630fc45d34b78fd253d0b5275ecfa85ce48125ef7275c3a9205d01b85d8",
	"0x1287f419048e81322d73bb9333e9b854e4ceac4b993b5342547263a486b42e34",
	"0x2a2f5a5a689471d5ef46d669e449ccdc1d37256618722f08cc2c7e75d06fc277",
	"0x38c913fdc729a28b7e354947f2b6449029976d442e349bc1c2acf3b0fa28bc92",
	"0x421826bc690adac2b1f3637bc5e2333cb5e4bce3f9e8eac1a0a76df32a7ebff7",
	"0x30ac2452c3a07bb924b6f7ed47cd6581499d532c5f90bf7fbc69556ff3bf6b09",
	"0x40ce93f92b281e538efbe7cec9a22a9c005eef428dde3cdd46191630f563ba04",
	"0x4fc3dd6720c87f672f7b6ff129e9b2a3236ec760a71f78aee84925d8e7616e97",
	"0x3f3ba6f9f12ca6f934f92b17f4f3bd8ec261e5870610557f687bc734eadaa2d4",
	"0x11d9eedda8d94fcbed859f5787fe20b7d4483cd319d8215530e2e316c89ee635",
	"0x29981cff92be6c882c89feb59849d014fcd163699b5b4fdafca335552c4581d1",
	"0x4c4fe2838d175c666c0d3f20d8dfefdcbcdacebca86e013d8ad29b6a0cf6bb79",
	"0x630428a99469c03f9027d3c601864185d360d920771ea950732cf000b869a09a",
	"0x46a776fbf1f36d7fdfa7a210cbb2ffa533540068c169e12f127cb14d9b587056",
	"0x41a775960677e6c5fdf73c2a409b6e5c08e271cbb8c825f598a1801c84fde5ae",
	"0x3086af931c41d791deb57f7f82dc511e4d349f42b52c3e0080097c4e44373dc8",
	"0x155516da7a229b61392a39cc10a67112f512203cab706428f5fbbb3a9fd89fbd",
	"0x41bdb1e32081ac55f42969658f78e308bdf50175b619c3ca8e3bfdf1ca984684",
	"0x01344d21e02b9c20d0d886a02167cf8502c3614ab909ae2fa7929b12d3e88519",
	"0x733a3e92f74b793915beab78e87bd88a2227aa5406df54dc9a2c5e80a11f71e5",
	"0x6a6cc17a31ba2fe1411cdebeb0809bf4ff0069b0d6ac681edf816ef4c59b6f64",
	"0x0a77e0a85b06c1b152098066bd36933264641627192e3acdbf611bd002918820",
	"0x3efb107ebed9b44672f679bffec0121fb509d19e97ae1bac3a86384e274c8c94",
	"0x3c0c4b441b0ea7ffe03c011db9aab4f86ec4849a0c783a3b7af21b05f5654482",
	"0x28072c7bfa64f6cb97e4341cd18809ef5cd083374fbec26370c2b0ac02dcdafe",
	"0x1962306e92b3c7295b2f7435ed8f67dda3a15ec6d8b0786d7727d071663ab22b",
	"0x594dc533611f7f588838f894a26b1cd27432c63f9fbe03ef2d95d9a2d191ae3f",
	"0x3e287fec491c686222949bc16c2308ade64e3a0a1dccdb25d64f9d5b94ead6e7",
	"0x2a95d47fb725b3978a7f90e601f2a9ab39074b35594e0bd133f9c5f34d765d42",
	"0x29c603ecc031a9750a4d826e4abf3874bc76c76cc7ea306b3b9636f9653ff58c",
	"0x0bbff6ba283aa42f01172bb82a2838e50941227abc3a2a5b1215b9a6d68de07c",
	"0x73c7ee55aaa453d36ed857353bc227375244a7e554ceeea2018eb9cb39a51e74",
	"0x3ff41b13d4cb3140ac8426322e88ff6f16895d88e6de3336cc88c693e0d38175",
	"0x03043688d4c991763362912a460be95b668fe9b1823fe90febfb3ffc7652ab24",
	"0x33a29a0d56a7a64d36a67da2c691ff3eaf8ec7f0d78b357e7d2254c5b0e28f73",
	"0x185db562fc75b43ba2710ad5e9114486b3e9712fe4c88f98b333c0c6211ac882",
	"0x147b89a0cff9083b8952b3ef292c683f75d523f932711c6e1db3f28f5163b1fb",
	"0x58ebc5d6b50bb1e4fdb4dcdfae1b69027978826f757ee4dc10d34f963f98fb59",
	"0x1318791367815809badf1f3ed677e50cef92021c65549b2dabaa52c7b424f5a9",
	"0x5bce78553694ba32f793c8d7f8d09ac63d0d7ada32b888d61b87849f3eda9557",
	"0x026bebcc38f0b2804ed21f2e2b16af2194375ff2559fbc588a8962caf0b684c0",
	"0x494bceff689f9885a3998de0eaaa7ac71a04522700f2e067efdbb037c6e53c66",
	"0x03ebaf5f0602347c4ed2bdb9a86eb955cb5cd5378f7a6f369dccb69792de8bd2",
	"0x3626d91f9f05334cb32d3a42eed03f7a553a0ed4cada2db08b45b548bd3b3655",
	"0x63ee9e5c5cd3c83e93757ed93358ff0583d761e595b62f11df27bd4292ffb6e5",
	"0x705dd80b2db4492c8b9984439b823681c4d9c8dcddcc04b9786a90051513a0e1",
	"0x2636ac2ac559be8fe509641dbc67e55db47bb051e05ef06301020c9501f110f1",
	"0x4781b8da302c7764951730e7ac0892de64537d94db2e19b84eec5a2d9539288e",
	"0x197852b9a62e16779725f35cd8daf52ffbc8cc9c902c16923f2ff8873795ca86",
	"0x1c3e49f33fd73480b280dba7744cf67e244449048f8fc84f7b6e452b4ede9a35",
	"0x41d20cdc6a15c07fd9735c89b155412fcbb7bd3cdfc27abaad2a3a8a90e99743",
	"0x0c3a7aaeb5f65d907944d7aa48c27648be3d0371bd97a9c060e8ef4f573521b8",
	"0x52ea7c3f75cba07991674295c4e1462108401b9a103736623943d42e4fbe334e",
	"0x1106537bf3150b442b0992ee517b69707c3042015e938f97a63d5c924e67f677",
	"0x71de967042516a5b990ef18ae9956fab89f361b950e0639963017c237ee2a0cf",
	"0x664a4487e02f7bfa07a1db6ab94a0d1ed0f9e74002bde9cfcbb65f6f74dbfca0",
	"0x1023721fd7285260935b5a347f167ce721dd6ae5004c4debc68066bac8f2c467",
	"0x2d52fbc95404515f5456c74b65186c860a89dcda8c84bf68fbf715f3d58fe3f2",
	"0x6d987c9de419fb6e075441fd99606303e765d8696bcfe01a0d11aa0bd47c8601",
	"0x422016ce4d744029b1440a288d7988e43d0f29d616c47f70322ff87cfbc69301",
	"0x1f82afe8eb16611abc6600f7dc2a72c8e1d39643c189f3caa1ead08241a896c4",
	"0x3bb8684cf815ae6d8a789e0e488c6fb2ac46883fe1cfeb8cfa6f3dbca0f954bd",
	"0x3d5a1a6e571306fac431b098cdb3c4518f5a8fc436535766fe9e1bb8bda95d1d",
	"0x5e36e175c5d7df42b86285f43b1e4c6bfbaca19f1019073d38d04de0d0647669",
	"0x2c3b1b86ce90cb3fe74c5c99b20c3314e28e2f07ce8d932030caee4dfe5055f1",
	"0x0bfba44d41c49044bce730d8af86fe0397fff85ec10288b847868d0e9834f754",
	"0x0b79924b9e44662369c615cc8d7f36fe4a4b2a79045cee61c413eaf91d82e0c2",
	"0x048a11ec75eb154b70223a40cc0db9104b13f6a4ca24e7b9707963ee6f9f74ef",
	"0x6dd58a400d366014e46b0b9785ce9d78516813ed2eb329dc4531bfbd8e80eec0",
	"0x112844b7c50e7e676b616e72539d5751dec5a063456921b6b16f9e930cc35ebc",
	"0x217b616b50e729547af8ceef5008d1edf8d90bc9a7f3ce7c9bc71867e1c06471",
	"0x3f9a0b8402ffa291bccbb46dcd2522dea790b35a8503da46717c63917dcb7b79",
	"0x42a44fc114c0cad9badf62b911610bdc4b1a0ba9f656f66173a5476e63dfce86",
	"0x294223972f4c7e9c9ebefebf059eb90f44479956f5337b12a2eb803e313e96cc",
	"0x448101837874eb1bda92bc8a632cbf8f70a0664bbcf3a196609b14c53ee4dbcb",
	"0x53a26c6e2b3df0b17faf6a259bc5531d3ae79da59eb8fc5f594e0b886d8d97be",
	"0x207c7c32631a75fe8e0da895367176d24e32c5573ec91acf235f3c6c307807cd",
	"0x20f955773b13b160d3575eb2380b466f7d38cb4a0e12a15d43d147645c3944ca",
];
pub const MDS_ENTRIES: [[&str; 5]; 5] = [
	[
		"0x354423b163d1078b0dd645be56316e34a9b98e52dcf9f469be44b108be46c107",
		"0x44778737e8bc1154aca1cd92054a1e5b83808403705f7d54da88bbd1920e1053",
		"0x5872eefb5ab6b2946556524168a2aebb69afd513a2fff91e50167b1f6e4055e0",
		"0x43dff85b25129835819bc8c95819f1a34136f6114e900cd3656e1b9e0e13f86a",
		"0x07803d2ffe72940596803f244ac090a9cf2d3616546520bc360c7eed0b81cbf8",
	],
	[
		"0x45d6bc4b818e2b9a53e0e2c0a08f70c34167fd8128e05ac800651ddfee0932d1",
		"0x08317abbb9e5046b22dfb79e64c8184855107c1d95dddd2b63ca10dddea9ff1a",
		"0x1bb80eba77c5dcffafb55ccba4ae39ac8f94a054f2a0ee3006b362f709d5e470",
		"0x038e75bdcf8be7fd3a1e844c4de7333531bbd5a8d2c3779627df88e7480e7c5c",
		"0x2dd797a699e620ea6b31b91ba3fad4a82f40cffb3e8a30c0b7a546ff69a9002b",
	],
	[
		"0x4b906f9ee339b196e958e3541b555b4b53e540a113b2f1cabba627be16eb5608",
		"0x605f0c707b82ef287f46431f9241fe4acf0b7ddb151803cbcf1e7bbd27c3e974",
		"0x100c514bf38f6ff10df1c83bb428397789cfff7bb0b1280f52343861e8c8737e",
		"0x2d40ce8af8a252f5611701c3d6b1e517161d0549ef27f443570c81fcdfe3706b",
		"0x3e6418bdf0313f59afc5f40b4450e56881110ea9a0532e8092efb06a12a8b0f1",
	],
	[
		"0x71788bf7f6c0cebae5627c5629d012d5fba52428d1f25cdaa0a7434e70e014d0",
		"0x55cc73296f7e7d26d10b9339721d7983ca06145675255025ab00b34342557db7",
		"0x0f043b29be2def73a6c6ec92168ea4b47bc9f434a5e6b5d48677670a7ca4d285",
		"0x62ccc9cdfed859a610f103d74ea04dec0f6874a9b36f3b4e9b47fd73368d45b4",
		"0x55fb349dd6200b34eaba53a67e74f47d08e473da139dc47e44df50a26423d2d1",
	],
	[
		"0x45bfbe5ed2f4a01c13b15f20bba00ff577b1154a81b3f318a6aff86369a66735",
		"0x6a008906685587af05dce9ad2c65ea1d42b1ec32609597bd00c01f58443329ef",
		"0x004feebd0dbdb9b71176a1d43c9eb495e16419382cdf7864e4bce7b37440cd58",
		"0x09f080180ce23a5aef3a07e60b28ffeb2cf1771aefbc565c2a3059b39ed82f43",
		"0x2f7126ddc54648ab6d02493dbe9907f29f4ef3967ad8cd609f0d9467e1694607",
	],
];
