import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/poseidon.circom
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/poseidon_constants.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

-- Poseidon constants for t=2,3,4 cases
namespace PoseidonConstants

def C_t2 : Vector ℕ 72 := #v[
  0x9c46e9ec68e9bd4fe1faaba294cba38a71aa177534cdd1b6c7dc0dbd0abd7a7,
  0xc0356530896eec42a97ed937f3135cfc5142b3ae405b8343c1d83ffa604cb81,
  0x250f5116a417d76aaa422952fcc5b33329f7714fc26d56c0432507fc740a87c4,
  0x264065ad87572e016659626c33c8213f7a373b9b8225a384f458d850bb4a949f,
  0x2bb8e94ad8d8adca6ce909ff94b8750729b294e4400376da39e33fda24bd42af,
  0x19051065d05d861ec813c15291d46a328f6201b21ad5d239d4f85fbb09a5dbae,
  0x245bd0617aa449618f5bd4550aac7b8e08d4d1c017165943cdf4776cdff3434a,
  0x9fb1a1118074ff79d8acbf5b02131e048a1570155e0f2b1c36ad091d491a88f,
  0x234ab504bbae8198972741952f78b7eb018ea192f05e54c1484ab8973ff66d88,
  0x1f66e509b84c355ae3d4c3513a282fd48f9c8c6439f42a7835fbcfe0f2a324c,
  0x1b22f5d69d725e6002cf00dd9ee62d1a5af0efdc4910f54127a920ccc43f91fa,
  0x252b55edead135f852968b7f1c4f490fa659ecd5b47a78a7db91f65a6dfc23f,
  0x1773ae2e1637c92ad0677c2a047fea8eca4b53303f21871f6892a2c0487d7ff1,
  0x2d57b02906cd0ab82a79e76faeef6f87666eac093cf7715645d5ec9f7ac732f5,
  0xa16f3a62824b281e8b2ddb8fc391a498fb061317faffa03696f834596313d93,
  0x1666f525f7f4b6988d2a37834ab747eae0587757b788eb7f1e26b08e36a08591,
  0x5da44f8e0a3b8bb13231f0ca25b50b57f5c82128e1dfec3e541d912ebe17b76,
  0x9a39ba9993303ba191bac8bdb3e0144dbfb5f39624cdd9524dc7861633bc95a,
  0x6c0fb824a19202d30ee6b418c0029e100e85a6d158f9f2a828dfd2ed0920a68,
  0x387d8e056b2b176a9776b4492cb3b418adc660627e52bb3324283bf9522395d,
  0x147a1af82036ef5b28a7a37bea40d6ac3013cf1b62358396bf7156f5c2dc9684,
  0x3038d92060daeaaf1bd0482bd3f0613d88e8dff90a7a0525f9227e4cb7c6f81b,
  0x72940aa1d538a5a39a323f9e5d65616cf6c223339006f9789a97245532908f5,
  0x2d3d604949f4e14c70b8a879aedec49b3a367ba216af048f464ed6f15e2b9023,
  0x225b9e4f35c7549f80774c2b4d18309b2dcf7c7287b982e49746a176641e73c5,
  0x1ea781288fdf13b2190095a2344828e37dfe81c75a09709f0d139bbbf6c70414,
  0x8e96c3e7e8de4432b202405458468b90dc6890d4cee128b3502e5b6cb4aeeeb,
  0x5b43da7c8aa29af6dcaae57d070b49d29ce889a64a4ac183e85d55b366c805f,
  0xbec98a034e3b8af7ba4861f1ad5a48dcef7c996e7a51c7cdde724d8f610e52,
  0x2eb67ccfa29e2b422b9f84a5d0575fc435b30fcae303039480be384ee4ebe72a,
  0x102bbdc21a3f147bf04eedee5d70bd084a7105c631c86ecd2c4e8749a13915ca,
  0x274bc16c88721babfd5bbe8d8562c1bf127ae38915280fbb8e3115cad3582f79,
  0x185cece417549b25283de04511f769101c8850b409d4928ab831611351bd9938,
  0x13c73fb043f7e978bc9cfb55c7faacb4f4c823674abe17737059ac0a32c36007,
  0x24b3a1d83308742b360c9c60595673e201cdd4cef5a4145c933c4e5969481d70,
  0x18b5ae94df9ec97aaa2a8f0f42425bcccdc8266a070f866ef0f48d7a3744398b,
  0x20eb398cb958cc2ccc7cb1fac38501abbe38169b2d8522d9e5f099f2d5905cb4,
  0x1e588dd3ec8b0d252c2c7c0c78a02b22bbbad1f4dcaa2e78a8b8eef2f4e29344,
  0xf8bf3bd6c22ba3b1bf3ab2e3fb40818cd4217ffbaf294ca42331d4e3043a0a6,
  0x388c9fcf30fc2841d648f46bad01dd10bee9dc184d25eabc9f617021109cec3,
  0x2bb7f397c5941ac67befa8b232f15c8853dac263da793555441a90cec83b6454,
  0x17f389b52f9ea7a98874a4a31ef6a7beb43fb17db0e499250bb3f0181c59fb21,
  0x3a2090eacb897a31fb10561d560a9aeec24b7ad14d17b145f20c875a0b28c7c,
  0xc398534f0eb580f1fe4bf64553389e67cca4714399430e09619dcbee17ba099,
  0x7095ac9fda46afa7f181259e3635feffa7f11ee63f3ee777a5cebf4822328c4,
  0x2046f7cf1c8f13ef2b69cbc8bc0d5d809f82568abe2b33d1cd060958b1ced683,
  0x2c274136a5de2849de6e7f92f9097296501acb68d56138fbcb660c4cb0f69107,
  0x1c4d5178acb5c6b6eceef23afc6f16ec7b0383094cb6467e8d0f4507b3cf74c3,
  0x65b1447d0d64ceced116785b92c63a6a7dd9701507dcbe8b909325e28f7b8d3,
  0x2265d7e244881220c81a193d979330409c9bfa333438951340e023e7b72a1961,
  0x15b12b355af7e05637a1c76e67f9cec6fca8a6449b37669f6850502256b30aba,
  0x1a1522fecc6ae028e4d3e3029497b88f35c2b48c687af168ec2582d9075b4387,
  0x22f56e79e81b7496e472a641a053c414bcc53b0a9350e2589240803076f58f26,
  0x202ddb66d0988994e7aabad692ceac4e2324672a17ab8417d1ee278afd17fd0c,
  0x12b0701e8813c5b21a8e30208f8f1158b96cd428ae77bdea72f84510f73edfce,
  0x1e63fd20e706e1407c8838ceb26b84c9fe693fdde0eb1e1a9df7e84e53eeee7e,
  0x20a16c5a86256deffd15af174c39f9d9aa11500676ac7e570088280dd1896259,
  0x1c8f8bf8e153da55ad5aca2eaaee38da563e0435c0f2f37c27558fb9bae0a3eb,
  0xd7732687bb7bf5f3aabcfdcc4fbb67e159c1983213e416c3880124fddf187c9,
  0xcdd04475a86999a2edcbbbf8264b195e108b3b60b6475d835f6ccef9e2f6865,
  0x2fe65586cd4e754b4c63a88c2ed3f9ba0e3bfa43f547b41153560c214fe3cbcd,
  0x503cf963c8273604e659128ec29261f62399815d98c56dbf4f2837c727ad4d9,
  0x1ee48ea27839061b78379936f6d97ca9400b393ef5fdf38ef1475c8742cb334c,
  0x1a423f8d8fc892b22d7cd5bf0197c575c579e83563d04859d73b2c1c5c0413f9,
  0x69a0da50133e9952f00e61778972a7be0e8d8ab76c95616ae465636abb97ec7,
  0x1bf7879dd42f2cbb91c65a0976356f67964c2f94dfbf0e44cf2b9909165d8614,
  0x1b23dccf485822065c8fc0afe610be7164e25056267f6c4a805fffd4547a0b98,
  0x2ebe90d6f6fdca420e0c2e004ce5c5a4409e564c9c4f3671e3011f627bec7c2e,
  0x167cd6930535a816dfebe81d20c376e77687760f3a2fa0da290b2f4d6c6863f7,
  0x8865c10f4a633c54ccc8b68b79df285f19f1210374cc64e3c8a966d4f90264b,
  0x1de902fbc0bf01951ca25abb39d78894721b37e071851b03a72cc6b833b7893b,
  0xe3eca007699dd0f852eb22da642e495f67c988dd5bf0137676b16a31eab4667
]

def C_t3 : Vector ℕ 81 := #v[
  0xee9a592ba9a9518d05986d656f40c2114c4993c11bb29938d21d47304cd8e6e,
  0xf1445235f2148c5986587169fc1bcd887b08d4d00868df5696fff40956e864,
  0x8dff3487e8ac99e1f29a058d0fa80b930c728730b7ab36ce879f3890ecf73f5,
  0x84d520e4e5bb469e1f9075cb7c490efa59565eedae2d00ca8ef88ceea2b0197,
  0x2d15d982d99577fa33da56722416fd734b3e667a2f9f15d8eb3e767ae0fd811e,
  0xed2538844aba161cf1578a43cf0364e91601f6536a5996d0efbe65632c41b6d,
  0x2600c27d879fbca186e739e6363c71cf804c877d829b735dcc3e3af02955e60a,
  0x28f8bd44a583cbaa475bd15396430e7ccb99a5517440dfd970058558282bf2c5,
  0x9cd7d4c380dc5488781aad012e7eaef1ed314d7f697a5572d030c55df153221,
  0x11bb6ee1291aabb206120ecaace460d24b6713febe82234951e2bee7d0f855f5,
  0x2d74e8fa0637d9853310f3c0e3fae1d06f171580f5b8fd05349cadeecfceb230,
  0x2735e4ec9d39bdffac9bef31bacba338b1a09559a511a18be4b4d316ed889033,
  0xf03c1e9e0895db1a5da6312faa78e971106c33f826e08dcf617e24213132dfd,
  0x17094cd297bf827caf92920205b719c18741090b8f777811848a7e9ead6778c4,
  0xdb8f419c21f92461fc2b3219465798348df90d4178042c81ba7d4b4d559e2b8,
  0x243443613f64ffa417427ed5933fcfbc66809db60b9ca1724a22709ceceeece2,
  0x22af49fbfd5d7e9fcd256c25c07d3dd8ecbbae6deecd03aa04bb191fada75411,
  0x14fbd37fa8ad6e4e0c78a20d93c7230c4677f797b4327323f7f7c097c19420e0,
  0x15a9298bbb882534d4b2c9fbc6e4ef4189420c4eb3f3e1ea22faa7e18b5ae625,
  0x2f7de75f23ddaaa5221323ebceb2f2ac83eef92e854e75434c2f1d90562232bc,
  0x36a4432a868283b78a315e84c4ae5aeca216f2ff9e9b2e623584f7479cd5c27,
  0x2180d7786a8cf810e277218ab14a11e5e39f3c962f11e860ae1c5682c797de5c,
  0xa268ef870736eebd0cb55be640d73ee3778990484cc03ce53572377eefff8e4,
  0x1eefefe11c0be4664f2999031f15994829e982e8c90e09069df9bae16809a5b2,
  0x27e87f033bd1e0a89ca596e8cb77fe3a4b8fb93d9a1129946571a3c3cf244c52,
  0x1498a3e6599fe243321f57d6c5435889979c4f9d2a3e184d21451809178ee39,
  0x27c0a41f4cb9fe67e9dd4d7ce33707f74d5d6bcc235bef108dea1bbebde507aa,
  0x1f75230908b141b46637238b120fc770f4f4ae825d5004c16a7c91fe1dae280f,
  0x25f99a9198e923167bba831b15fffd2d7b97b3a089808d4eb1f0a085bee21656,
  0x101bc318e9ea5920d0f6acdc2bb526593d3d56ec8ed14c67622974228ba900c6,
  0x1a175607067d517397c1334ecb019754ebc0c852a3cf091ec1ccc43207a83c76,
  0xf02f0e6d25f9ea3deb245f3e8c381ee6b2eb380ba4af5c1c4d89770155df37b,
  0x151d757acc8237af08d8a6677203ec9692565de456ae789ff358b3163b393bc9,
  0x256cd9577cea143049e0a1fe0068dd20084980ee5b757890a79d13a3a624fad4,
  0x513abaff6195ea48833b13da50e0884476682c3fbdd195497b8ae86e1937c61,
  0x1d9570dc70a205f36f610251ee6e2e8039246e84e4ac448386d19dbac4e4a655,
  0x18f1a5194755b8c5d5d7f1bf8aaa6f56effb012dd784cf5e044eec50b29fc9d4,
  0x266b53b615ef73ac866512c091e4a4f2fa4bb0af966ef420d88163238eebbca8,
  0x2d63234c9207438aa42b8de27644c02268304dfeb8c89a1a3f4fd6e8344ae0f7,
  0x2ab30fbe51ee49bc7b3adde219a6f0b5fbb976205ef8df7e0021daee6f55c693,
  0x1aee6d4b3ebe9366dcb9cce48969d4df1dc42abcd528b270068d9207fa6a45c9,
  0x1891aeab71e34b895a79452e5864ae1d11f57646c60bb34aa211d123f6095219,
  0x24492b5f95c0b0876437e94b4101c69118e16b2657771bd3a7caab01c818aa4b,
  0x1752161b3350f7e1b3b2c8663a0d642964628213d66c10ab2fddf71bcfde68f,
  0xab676935722e2f67cfb84938e614c6c2f445b8d148de54368cfb8f90a00f3a7,
  0xb0f72472b9a2f5f45bc730117ed9ae5683fc2e6e227e3d4fe0da1f7aa348189,
  0x16aa6f9273acd5631c201d1a52fc4f8acaf2b2152c3ae6df13a78a513edcd369,
  0x2f60b987e63614eb13c324c1d8716eb0bf62d9b155d23281a45c08d52435cd60,
  0x18d24ae01dde92fd7606bb7884554e9df1cb89b042f508fd9db76b7cc1b21212,
  0x4fc3bf76fe31e2f8d776373130df79d18c3185fdf1593960715d4724cffa586,
  0xd18f6b53fc69546cfdd670b41732bdf6dee9e06b21260c6b5d26270468dbf82,
  0xba4231a918f13acec11fbafa17c5223f1f70b4cdb045036fa5d7045bd10e24,
  0x7b458b2e00cd7c6100985301663e7ec33c826da0635ff1ebedd0dd86120b4c8,
  0x1c35c2d96db90f4f6058e76f15a0c8286bba24e2ed40b16cec39e9fd7baa5799,
  0x1d12bea3d8c32a5d766568f03dd1ecdb0a4f589abbef96945e0dde688e292050,
  0xd953e20022003270525f9a73526e9889c995bb62fdea94313db405a61300286,
  0x29f053ec388795d786a40bec4c875047f06ff0b610b4040a760e33506d2671e1,
  0x4188e33735f46b14a4952a98463bc12e264d5f446e0c3f64b9679caaae44fc2,
  0x149ec28846d4f438a84f1d0529431bb9e996a408b7e97eb3bf1735cdbe96f68f,
  0xde20fae0af5188bca24b5f63630bad47aeafd98e651922d148cce1c5fdddee8,
  0x12d650e8f790b1253ea94350e722ad2f7d836c234b8660edf449fba6984c6709,
  0x22ab53aa39f34ad30ea96717ba7446aafdadbc1a8abe28d78340dfc4babb8f6c,
  0x26503e8d4849bdf5450dabea7907bc3de0de109871dd776904a129db9149166c,
  0x1d5e7a0e2965dffa00f5454f5003c5c8ec34b23d897e7fc4c8064035b0d33850,
  0xee3d8daa098bee012d96b7ec48448c6bc9a6aefa544615b9cb3c7bbd07104cb,
  0x1bf282082a04979955d30754cd4d9056fa9ef7a7175703d91dc232b5f98ead00,
  0x7ae1344abfc6c2ce3e951bc316bee49971645f16b693733a0272173ee9ad461,
  0x217e3a247827c376ec21b131d511d7dbdc98a36b7a47d97a5c8e89762ee80488,
  0x215ffe584b0eb067a003d438e2fbe28babe1e50efc2894117509b616addc30ee,
  0x1e770fc8ecbfdc8692dcedc597c4ca0fbec19b84e33da57412a92d1d3ce3ec20,
  0x2f6243cda919bf4c9f1e3a8a6d66a05742914fc19338b3c0e50e828f69ff6d1f,
  0x246efddc3117ecd39595d0046f44ab303a195d0e9cc89345d3c03ff87a11b693,
  0x53e8d9b3ea5b8ed4fe006f139cbc4e0168b1c89a918dfbe602bc62cec6adf1,
  0x1b894a2f45cb96647d910f6a710d38b7eb4f261beefff135aec04c1abe59427b,
  0xaeb1554e266693d8212652479107d5fdc077abf88651f5a42553d54ec242cc0,
  0x16a735f6f7209d24e6888680d1781c7f04ba7d71bd4b7d0e11faf9da8d9ca28e,
  0x487b8b7fab5fc8fd7c13b4df0543cd260e4bcbb615b19374ff549dcf073d41b,
  0x1e75b9d2c2006307124bea26b0772493cfb5d512068c3ad677fdf51c92388793,
  0x5120e3d0e28003c253b46d5ff77d272ae46fa1e239d1c6c961dcb02da3b388f,
  0xda5feb534576492b822e8763240119ac0900a053b171823f890f5fd55d78372,
  0x2e211b39a023031a22acc1a1f5f3bb6d8c2666a6379d9d2c40cc8f78b7bd9abe
]

def C_t4 : Vector ℕ 88 := #v[
  0x19b849f69450b06848da1d39bd5e4a4302bb86744edc26238b0878e269ed23e5,
  0x265ddfe127dd51bd7239347b758f0a1320eb2cc7450acc1dad47f80c8dcf34d6,
  0x199750ec472f1809e0f66a545e1e51624108ac845015c2aa3dfc36bab497d8aa,
  0x157ff3fe65ac7208110f06a5f74302b14d743ea25067f0ffd032f787c7f1cdf8,
  0x1b0f68f0726a0514a4d05b377b58aabc45945842e70183784a4ab5a32337b8f8,
  0x1228d2565787140430569d69342d374d85509dea4245db479fdef1a425e27526,
  0x17a8784ecdcdd6e550875c36a89610f7b8c1d245d52f53ff96eeb91283585e0b,
  0x9870a8b450722a2b2d5ee7ae865aaf0aa00adcfc31520a32e0ceaa250aaebaf,
  0x1e1d6aaa902574e3e4055c6b6f03a49b2bbdb7847f940ebc78c0a6d3f9372a64,
  0x2816c4fa6b085487e1eec1eefd92ee9fef40f30190ac61009103d03266550db2,
  0x17359fd88be36ba867000e83f76ffb46660634efbad15dcf4d4d502d427ff51c,
  0xe3004cb44ba455a3f16fefbd0c026404cbac203c0f236baad879610b8661022,
  0xa55f276af1ceb6ebc6c6820f334b26f11ca4af98c833bc1b496193d6b04a7ca,
  0x1ee4b0458adcd4c4861a27adc1404a5981d320b6b8e20e51d31b9b877e8346d,
  0x14315e2753e7fb94f70199f8645d78f87c194a4054e69872b3841da1b4f482f1,
  0x2b7b63ecffd55d95c660f435ad9e2e25f266cb57e17ebd1b6b0d75e88a6a56d6,
  0xbb56fa3e9fd48ab46d4e7295bbe1204b652ebe958221860f56e38db80d83c0,
  0x50653bf5dd59edd6d15fa6071f5005057218b33a8f92a58b9c2656081249f82,
  0x2c575423e24b522655c5a976c65d069287900c8d5825514098c5b13c86f1fcdc,
  0x2ff3a2ccdee91e09a32f74232b704cdd99f72c1f78557a2ce568b07e218071d7,
  0x1144734901a81c1543b8bc6fc9d365f50469eb89949491d3693dbe9c6238d90c,
  0x1eff9a954e24bcd4af20b6ab74d89e1cd38bc694a9e75ea6da217a98db80cd22,
  0x14707de7496c5638f97fe9bd7d485c20ead6bfdbfc0599791e49fad0301cd6df,
  0x13d0de341ba819f90fe3ef1f7ce0a54d8538acdd9b3ef840a91d48ee536042b8,
  0x26520ab1d20055daded712d59b07088458c18afbd0da58aee9f151a903372ba1,
  0x68cb4827ac485fc6e7537a3c0a06d08a4c2790f5c65d9866d75296999f7495f,
  0x7d6baaa2e587c21b03dfa0eb71136e2982cb389b438c8bc282748d0e674e89e,
  0x15b92d36db02cb16b831eeab2e6ed75d126ffbc274cc3362370851526de13d27,
  0x277b9ce89133de7b7918ad5fcfab7323ef5b9c1916b588cd7e5a0d814cbc3395,
  0x2ae847b66b3c5d73b70b733040aa86c51f737092d65c3492d529000fa1802b24,
  0x2fa3e8ae1fef974cded6aba6dc25cf567e16e0af29e675706643f21bf8efd651,
  0xb1d4b9508cec4d19aa53f4efe46c57952dbd368fcbcd454a8b1087bc18a2088,
  0x2d381014d01578b888b3273270babdc393ac392e7958be0478947fafa569bb0,
  0x2e79a827c85406242523a94431007021bc865a45cabcba4368c41d4486fefec8,
  0x207c99b7d594a5c61d7e60cc2365c4c0c804cd434098af6244f0a00c259b347,
  0x119c124086ea58ebb83f14f262c693424360e97e6fb42ae8596badbe9edb2dca,
  0x104ff38cca0f00173ccd0b68bddba09fc543f074f753bd8e413f8334f887a251,
  0x2f5b5377bd156f89845811eb262436638dc038b8cb10e147a87df4c0e2384253,
  0xf70e8e02d1d23968930a8e0db69b1c20204f3e3b4cecd101f81476d0b5ea996,
  0x1ac4653a51071ae722f90a03f006d8575814db782b7f19f607dae4d56ad586b3,
  0x12b12600e3bfd8e7bdfae5ef9c4f3805fa41e74acabf7de817823017a8b23db9,
  0x11b9d19908919dacb7e0f8d0ba77286d417529a18a1d89c405ed1c30289fdd28,
  0x2c350d245f4f75864744f88dbff8fe335b00f4fb688895c1363a7484ace820d3,
  0x16a7f76fd2b2147db6ef94c22c78bff782de17ef73e52da7df82603f422b461f,
  0x1d18d8024be1e96ec25626af06a139f6093545aa504033dac7e285d1cc3db3de,
  0xc8cab1ad5998072945b9b88228f53c295466819fb94d8f6a9ed449be8f7c18c,
  0x1a68d133d703cd406ca30041913ce3423c73b13384187ab1530109b756ad4f7a,
  0x24a58b9e86ce823ff4c45342941417ff23d03c80fcdef9498ca0d860855e01a9,
  0xe6315c93fbb89d38021148b6c35320fb793c41c6a4386d6aed6acfe2f952c57,
  0x2c3806d99a69ce63299e876f5f218c7295d87224795d7568d558696e34c692f8,
  0x59c893a771e94774d49a356494568dd376856ab89705dff25db8273860fa04e,
  0x1166d9819c4faae8982243d0deb1f8977027d5cc56bf52ce260bec5e27e8b0f5,
  0x12806fab3fcb09fc2b79406c3c203c4965fc7259112af2104312e1537327e0a3,
  0x172015e0e33736058f60aa33e82d3dd73dc3ead89f98ded0dba35dcc1d8bda2c,
  0x77ba18800d852d0a34f70ae8cfd68a080296bf9d47a1b40de7e6fd6392a0d30,
  0x2094ecd768bfa8f0df0d78d0d946e1aff4a2d38e029e41479d6e3c0fe79fa8b9,
  0xccebd302afe84c20ff774d3c1f650ca7cd0bca08baa1e261da9c7441a823f89,
  0x5b9303053bb40c73671f5d55b4052e0d5549871f1b5283f01485a6b568cd05,
  0x2527289084ab492275b4cd67d38311a2b816eaa68ee6bdb2389eeefd6ba4c721,
  0x2222f9738290d8d5f2a3eacdad95f12cd4e7417ed2661b012f6448c7503877f2,
  0x226c8208f26d69e6b7e02fe26557e6bd160fcbe27ee741fd1e581161c1789354,
  0x216b208c0261f3c91faf609e15f7a9d4853e40d9204496b2441115d73c2941c5,
  0xe0d660e046a259f3bad6829729b6ae3151fbcd75de33b122fe134ca3d5a4dd6,
  0x240f039d2026b3266f39ba5c4ec48ac6ace88aadaef991498cd52daaa0ffbba8,
  0x28c8cccf7b40a2c3cfd2eee0ec4d160a876a4dfeb408ffe333e92fa5e1ee4d79,
  0xd7f81b4b46d4f247c4243f045a852cc957d2b2923d28eb2fa77b5a9844efd69,
  0x2be432f87b2c5094a82c788457651dd8cdb0200ac3b42860cbf54475996b772f,
  0x13ea39f2d63d9adae187af14dd07b533d45a63435e0ea4e5e555d35e70d4016b,
  0x29e3b1afe1973be9cd1cf4b047325abfaa65cf2b98ff3aed47870461977ec921,
  0x8db7d684e6b841b5e9692498f95a1f950a1cf1eb638bb4e48f3bc1a3c571197,
  0xf4f1041a976aa05196da1c042124e3277ea1a28fb6eeeab4bec1243bd31618b,
  0x5a9d0526d6f18c86b255f00e86ec34e7f8a26c251b51c21fe4c12bdc4c0ff1d,
  0x284b0304dd6ce669bcf650c5ab85c89d4410d472aa6eb00df1b8d17e52f2f3ff,
  0x2363e9b01a0163598962ff86907002f95902e725049294ca7ab10cc7aa3f06ba,
  0x2c2db12647c4c0461dd3290a75c5f2fd8d7f115b3e040cb05dd7e3ad260d842,
  0x2e3c42f671431f9560f3d0863ac445052422d5b993e9fda6b81486b14ffe3a74,
  0x1d38441f228c0ce22ff2882560f5d7ee3b4c0caa101371cb7782ffd97af5fff1,
  0x268141b0e49c59eab1d573ead4e2e1f379364dd133f2cec574c25ade2c794287,
  0x2209cb2e187df1522810d3f28868da6cf52af9a65dbd7b806049f472d966374a,
  0xa5eb2510e6f804d1830d7974ac1677d082034e5388bfaee91a319eca7c1ffab,
  0x1cb2864c38800736f8f3ad98669d3ad7a9d5ee52138e96b8a7015e1089e36ae0,
  0x2af8ed05bfc8f8ada547ee9bc6c7c6c5e8c15c6c0d380a3f9aa277273321b54e,
  0xf85d1593b35be03f79b222885555a252bf1f0a3911d784132c49b1a96ac0f3c,
  0x29095192ec53e0b859eba456295d95bc4567d351a6dad391b8b89707855008c5,
  0x1a92efde1f5fa56aeb02b4c4b8f51ac80831f898c7843407113fbb6011177854,
  0x2a05e8deeea15e4377c080aa70fd6a86dc73f3fdfa6b55f5610614c184b0b02e,
  0x12119f3b019cc3fc46ecc80893e86f510b1dd4030b2ce28c9dadcd1e71ad4891,
  0x42b6ffe687bc23a2bf6b73317286a543c60ed122fc225aae742c3a1c2dd3a1d
]

def length : ℕ → ℕ
| 2 => 72
| 3 => 81
| 4 => 88
| _ => 0  -- Placeholder for unsupported cases

-- Round constants function
def poseidon_C (t : ℕ) : Vector ℕ (length t) :=
  if h : t = 2 then
    C_t2.cast (by simp [length, h])
  else if h' : t = 3 then
    C_t3.cast (by simp [length, h', h])
  else if h'' : t = 4 then
    C_t4.cast (by simp [length, h''])
  else
    #v[].cast (by simp [length, h, h', h'', h''])

-- For now, we'll use identity matrices for M and P for simplicity
def poseidon_M (t : ℕ) : Vector (Vector ℕ t) t :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then 1 else 0

def poseidon_P (t : ℕ) : Vector (Vector ℕ t) t :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then 1 else 0

-- Simplified S constants (would need full implementation for production)
def poseidon_S (t : ℕ) : Vector ℕ (if t = 2 then 56 else if t = 3 then 112 else 120) :=
  Vector.ofFn fun _ => 0

end PoseidonConstants

namespace Sigma
/-
template Sigma() {
    signal input in;
    signal output out;

    signal in2;
    signal in4;

    in2 <== in*in;
    in4 <== in2*in2;

    out <== in4*in;
}
-/
def main (input : Expression (F p)) := do
  let in2 ← witnessField fun env => (input * input).eval env
  in2 === input * input

  let in4 ← witnessField fun env => (in2 * in2).eval env
  in4 === in2 * in2

  let out ← witnessField fun env => (in4 * input).eval env
  out === in4 * input

  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 3
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions _ := True
  Spec (input : F p) output := output = input^5

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Sigma

namespace Ark
/-
template Ark(t, C, r) {
    signal input in[t];
    signal output out[t];

    for (var i=0; i < t; i++) {
        out[i] <== in[i] + C[i + r];
    }
}
-/
def main (t : ℕ) (constants : Vector (F p) (PoseidonConstants.length t)) (round_offset : ℕ)
    (input : Vector (Expression (F p)) t) := do
  -- First define the entire Vector of Expressions
  let out' : fields t (Expression (F p)) := Vector.ofFn fun i =>
    let c_idx := round_offset + i.val
    if h : c_idx < constants.size then
      have h' : c_idx < PoseidonConstants.length t := by
        simp only [Vector.size_toArray] at h ⊢
        exact h
      input[i] + constants[c_idx]'h'
    else
      input[i]

  -- Then witness it and constrain to be equal with a single === command
  let out : fields t (Expression (F p)) ← witness fun env => eval env out'
  out === out'

  return out

def circuit (t : ℕ) (constants : Vector (F p) (PoseidonConstants.length t)) (round_offset : ℕ)
    : FormalCircuit (F p) (fields t) (fields t) where
  main := main t constants round_offset
  localLength _ := t  -- Just the witness for out vector
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := sorry

  Assumptions _ := True
  Spec input output := ∀ i (_ : i < t), output[i] = input[i] + constants[round_offset + i]'sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Ark

namespace Mix
/-
template Mix(t, M) {
    signal input in[t];
    signal output out[t];

    var lc;
    for (var i=0; i < t; i++) {
        lc = 0;
        for (var j=0; j < t; j++) {
            lc += M[j][i]*in[j];
        }
        out[i] <== lc;
    }
}
-/
def Matrix (F : Type) (t : ℕ)  := Vector (Vector F t) t

def main (t : ℕ) (matrix : Matrix (F p) t)
    (input : Vector (Expression (F p)) t) : Circuit (F p) (Vector (Expression (F p)) t) := do
  sorry

def circuit (t : ℕ) (matrix : Matrix (F p) t) :
    FormalCircuit (F p) (fields t) (fields t) where
  main := main t matrix
  localLength _ := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Assumptions _ := True
  Spec input output := sorry
  soundness := sorry
  completeness := sorry
end Mix

namespace MixLast
/-
template MixLast(t, M, s) {
    signal input in[t];
    signal output out;

    var lc = 0;
    for (var j=0; j < t; j++) {
        lc += M[j][s]*in[j];
    }
    out <== lc;
}
-/
def main (t : ℕ) (matrix : Vector (Vector (F p) t) t) (s : ℕ)
    (input : Vector (Expression (F p)) t) := do
  -- Matrix multiply to get the s-th output element
  let out ← witnessField fun _ => (0 : F p)  -- placeholder
  return out

def circuit (t : ℕ) (matrix : Vector (Vector (F p) t) t) (s : ℕ)
    : FormalCircuit (F p) (fields t) field where
  main := main t matrix s
  localLength _ := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Assumptions _ := True
  Spec input output := sorry
  soundness := sorry
  completeness := sorry
end MixLast

namespace MixS
/-
template MixS(t, S, r) {
    signal input in[t];
    signal output out[t];

    var lc = 0;
    for (var i=0; i < t; i++) {
        lc += S[(t*2-1)*r+i]*in[i];
    }
    out[0] <== lc;
    for (var i=1; i < t; i++) {
        out[i] <== in[i] +  in[0] * S[(t*2-1)*r + t + i -1];
    }
}
-/
def main (t : ℕ) (s_constants : Vector (F p) (if t = 2 then 56 else if t = 3 then 112 else 120)) (r : ℕ)
    (input : Vector (Expression (F p)) t) : Circuit (F p) (Vector (Expression (F p)) t) :=
  sorry

def circuit (t : ℕ) (s_constants : Vector (F p) (if t = 2 then 56 else if t = 3 then 112 else 120)) (r : ℕ)
    : FormalCircuit (F p) (fields t) (fields t) where
  main := main t s_constants r
  localLength _ := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Assumptions _ := True
  Spec input output := sorry
  soundness := sorry
  completeness := sorry
end MixS

namespace PoseidonEx
/-
template PoseidonEx(nInputs, nOuts) {
    signal input inputs[nInputs];
    signal input initialState;
    signal output out[nOuts];

    // Using recommended parameters from whitepaper https://eprint.iacr.org/2019/458.pdf (table 2, table 8)
    // Generated by https://extgit.iaik.tugraz.at/krypto/hadeshash /blob/master/code/calc_round_numbers.py
    // And rounded up to nearest integer that divides by t
    var N_ROUNDS_P[16] = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
    var t = nInputs + 1;
    var nRoundsF = 8;
    var nRoundsP = N_ROUNDS_P[t - 2];
    var C[t*nRoundsF + nRoundsP] = POSEIDON_C(t);
    var S[  N_ROUNDS_P[t-2]  *  (t*2-1)  ]  = POSEIDON_S(t);
    var M[t][t] = POSEIDON_M(t);
    var P[t][t] = POSEIDON_P(t);

    component ark[nRoundsF];
    component sigmaF[nRoundsF][t];
    component sigmaP[nRoundsP];
    component mix[nRoundsF-1];
    component mixS[nRoundsP];
    component mixLast[nOuts];


    ark[0] = Ark(t, C, 0);
    for (var j=0; j<t; j++) {
        if (j>0) {
            ark[0].in[j] <== inputs[j-1];
        } else {
            ark[0].in[j] <== initialState;
        }
    }

    for (var r = 0; r < nRoundsF\2-1; r++) {
        for (var j=0; j < t; j++) {
            sigmaF[r][j] = Sigma();
            if(r==0) {
                sigmaF[r][j].in <== ark[0].out[j];
            } else {
                sigmaF[r][j].in <== mix[r-1].out[j];
            }
        }

        ark[r+1] = Ark(t, C, (r+1)*t);
        for (var j=0; j < t; j++) {
            ark[r+1].in[j] <== sigmaF[r][j].out;
        }

        mix[r] = Mix(t,M);
        for (var j=0; j < t; j++) {
            mix[r].in[j] <== ark[r+1].out[j];
        }

    }

    for (var j=0; j < t; j++) {
        sigmaF[nRoundsF\2-1][j] = Sigma();
        sigmaF[nRoundsF\2-1][j].in <== mix[nRoundsF\2-2].out[j];
    }

    ark[nRoundsF\2] = Ark(t, C, (nRoundsF\2)*t );
    for (var j=0; j < t; j++) {
        ark[nRoundsF\2].in[j] <== sigmaF[nRoundsF\2-1][j].out;
    }

    mix[nRoundsF\2-1] = Mix(t,P);
    for (var j=0; j < t; j++) {
        mix[nRoundsF\2-1].in[j] <== ark[nRoundsF\2].out[j];
    }


    for (var r = 0; r < nRoundsP; r++) {
        sigmaP[r] = Sigma();
        if (r==0) {
            sigmaP[r].in <== mix[nRoundsF\\2-1].out[0];
        } else {
            sigmaP[r].in <== mixS[r-1].out[0];
        }

        mixS[r] = MixS(t, S, r);
        for (var j=0; j < t; j++) {
            if (j==0) {
                mixS[r].in[j] <== sigmaP[r].out + C[(nRoundsF\2+1)*t + r];
            } else {
                if (r==0) {
                    mixS[r].in[j] <== mix[nRoundsF\2-1].out[j];
                } else {
                    mixS[r].in[j] <== mixS[r-1].out[j];
                }
            }
        }
    }

    for (var r = 0; r < nRoundsF\2-1; r++) {
        for (var j=0; j < t; j++) {
            sigmaF[nRoundsF\2 + r][j] = Sigma();
            if (r==0) {
                sigmaF[nRoundsF\2 + r][j].in <== mixS[nRoundsP-1].out[j];
            } else {
                sigmaF[nRoundsF\2 + r][j].in <== mix[nRoundsF\2+r-1].out[j];
            }
        }

        ark[ nRoundsF\2 + r + 1] = Ark(t, C,  (nRoundsF\2+1)*t + nRoundsP + r*t );
        for (var j=0; j < t; j++) {
            ark[nRoundsF\2 + r + 1].in[j] <== sigmaF[nRoundsF\2 + r][j].out;
        }

        mix[nRoundsF\2 + r] = Mix(t,M);
        for (var j=0; j < t; j++) {
            mix[nRoundsF\2 + r].in[j] <== ark[nRoundsF\2 + r + 1].out[j];
        }

    }

    for (var j=0; j < t; j++) {
        sigmaF[nRoundsF-1][j] = Sigma();
        sigmaF[nRoundsF-1][j].in <== mix[nRoundsF-2].out[j];
    }

    for (var i=0; i < nOuts; i++) {
        mixLast[i] = MixLast(t,M,i);
        for (var j=0; j < t; j++) {
            mixLast[i].in[j] <== sigmaF[nRoundsF-1][j].out;
        }
        out[i] <== mixLast[i].out;
    }

}
-/
def main (nInputs nOuts : ℕ)
    (inputs : Vector (Expression (F p)) nInputs)
    (initialState : Expression (F p)) : Circuit (F p) (Vector (Expression (F p)) nOuts) := do
  sorry

def circuit (nInputs nOuts : ℕ)
    : FormalCircuit (F p) (fields (nInputs + 1)) (fields nOuts) where
  main input := sorry
  localLength _ := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Assumptions _ := True
  Spec input output := sorry
  soundness := sorry
  completeness := sorry
end PoseidonEx

namespace Poseidon
/-
template Poseidon(nInputs) {
    signal input inputs[nInputs];
    signal output out;

    component pEx = PoseidonEx(nInputs, 1);
    pEx.initialState <== 0;
    for (var i=0; i < nInputs; i++) {
        pEx.inputs[i] <== inputs[i];
    }
    out <== pEx.out[0];
}
-/
def main (nInputs : ℕ)
    (inputs : Vector (Expression (F p)) nInputs) : Circuit (F p) (Expression (F p)) := do
  sorry

def circuit (nInputs : ℕ)
    : FormalCircuit (F p) (fields nInputs) field where
  main := main nInputs
  localLength _ := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Assumptions _ := True
  Spec input output := sorry
  soundness := sorry
  completeness := sorry
end Poseidon

end Circomlib
