#include <zig.h>
typedef struct {
 zig_u8 const * ptr;
 zig_usize len;
} zig_L_u8;
typedef zig_u8 zig_A_u8_8[zig_as_u32(8)];
typedef zig_u8 zig_A_u8_1[zig_as_u32(1)];
typedef zig_u8 zig_A_u8_4[zig_as_u32(4)];
typedef struct {
 zig_u8 * ptr;
 zig_usize len;
} zig_L_u8;
typedef struct zig_S_builtin_StackTrace__277 zig_S_builtin_StackTrace__277;
typedef struct {
 zig_usize payload;
 zig_bool is_null;
} zig_Q_usize;
typedef struct zig_S_rand_Xoshiro256__255 zig_S_rand_Xoshiro256__255;
struct zig_S_rand_Xoshiro256__255 {
 zig_u64 s[zig_as_u32(4)];
};
typedef zig_u64 zig_A_u64_4[zig_as_u32(4)];
typedef struct {
 zig_u32 f0;
 zig_u8 f1;
} zig_T_tuple_7bu32_2c_20u1_7d;
typedef struct zig_S_target_Target_Cpu_Feature_Set__1123 zig_S_target_Target_Cpu_Feature_Set__1123;
struct zig_S_target_Target_Cpu_Feature_Set__1123 {
 zig_usize ints[zig_as_u32(9)];
};
typedef zig_usize zig_A_usize_9[zig_as_u32(9)];
typedef struct zig_S_target_Target_Cpu_Model__1116 zig_S_target_Target_Cpu_Model__1116;
struct zig_S_target_Target_Cpu_Model__1116 {
 zig_L_u8 name;
 zig_L_u8 llvm_name;
 zig_S_target_Target_Cpu_Feature_Set__1123 features;
};
typedef struct zig_S_target_Target_Cpu__1087 zig_S_target_Target_Cpu__1087;
struct zig_S_target_Target_Cpu__1087 {
 zig_u8 arch;
 zig_S_target_Target_Cpu_Model__1116 const * model;
 zig_S_target_Target_Cpu_Feature_Set__1123 features;
};
typedef struct {
 zig_u8 const * ptr;
 zig_usize len;
} zig_L_target_mips_Feature;
typedef struct {
 zig_usize f0;
 zig_u8 f1;
} zig_T_tuple_7busize_2c_20u1_7d;
typedef struct zig_S_rand_Random__343 zig_S_rand_Random__343;
typedef zig_void (*zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void)(zig_void * , zig_L_u8 );
struct zig_S_rand_Random__343 {
 zig_void * ptr;
 zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void fillFn;
};
typedef struct {
 zig_u8 f0;
 zig_u8 f1;
} zig_T_tuple_7bu7_2c_20u1_7d;
typedef zig_i32 zig_A_i32_65536[zig_as_u32(65536)];
typedef struct {
 zig_i32 f0;
 zig_u8 f1;
} zig_T_tuple_7bi32_2c_20u1_7d;
typedef struct {
 zig_u8 f0;
 zig_u8 f1;
} zig_T_tuple_7bu8_2c_20u1_7d;
typedef struct {
 zig_isize f0;
 zig_u8 f1;
} zig_T_tuple_7bisize_2c_20u1_7d;
typedef struct zig_S_rand_SplitMix64__330 zig_S_rand_SplitMix64__330;
struct zig_S_rand_SplitMix64__330 {
 zig_u64 s;
};
enum {
 zig_error__28no_20error_29 = 0u,
};
static zig_u8 const zig_errorName__28no_20error_29[zig_as_u32(11)] = {zig_as_u8(40),zig_as_u8(110),zig_as_u8(111),zig_as_u8(32),zig_as_u8(101),zig_as_u8(114),zig_as_u8(114),zig_as_u8(111),zig_as_u8(114),zig_as_u8(41),zig_as_u8(0)};
static zig_L_u8 const zig_errorName[zig_as_u32(1)] = {{zig_errorName__28no_20error_29, zig_as_u32(10)}};
static zig_u8 rand_Random_init__anon_747_gen_fill__anon_1447[zig_as_u32(19)];
static zig_u8 debug_assert__anon_1446[zig_as_u32(24)];
static zig_u8 generator_isSpaceForTree__anon_1443[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1442[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1441[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1440[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1439[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1438[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1437[zig_as_u32(16)];
static zig_u8 generator_isSpaceForTree__anon_1436[zig_as_u32(16)];
static zig_u8 target_Target_Cpu_Arch_endian__anon_1432[zig_as_u32(23)];
static zig_u8 target_Target_Cpu_Feature_Set_addFeature__anon_1431[zig_as_u32(27)];
static zig_u8 target_Target_Cpu_Feature_feature_set_fns_28target_mips_Feature_29_featureSet__anon_1430[zig_as_u32(16)];
static zig_u8 rand_Random_init__anon_747__anon_1429[zig_as_u32(30)];
static zig_u8 rand_Xoshiro256_fill__anon_1319[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1318[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1317[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1316[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1315[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1314[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1313[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1312[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1311[zig_as_u32(16)];
static zig_u8 rand_Xoshiro256_fill__anon_1309[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1308[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1307[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1306[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1305[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1304[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1303[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1302[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1301[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1300[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1299[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1298[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1297[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1296[zig_as_u32(16)];
static zig_u8 perlin_noise__anon_1295[zig_as_u32(50)];
static zig_u8 perlin_noise__anon_1294[zig_as_u32(50)];
static zig_u8 perlin_noise__anon_1293[zig_as_u32(50)];
static zig_u8 perlin_noise__anon_1292[zig_as_u32(50)];
static zig_u8 perlin_noise__anon_1291[zig_as_u32(50)];
static zig_u8 perlin_noise__anon_1290[zig_as_u32(50)];
static zig_u8 generator_growTree__anon_1289[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1288[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1287[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1286[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1285[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1284[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1283[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1282[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1281[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1280[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1279[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1278[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1277[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1276[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1275[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1274[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1273[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1272[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1271[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1270[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1269[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1268[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1267[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1266[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1265[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1264[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1263[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1262[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1261[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1260[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1259[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1258[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1257[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1256[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1255[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1254[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1253[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1252[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1251[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1250[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1249[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1248[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1247[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1246[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1245[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1244[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1243[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1242[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1241[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1240[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1239[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1238[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1237[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1236[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1235[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1234[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1233[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1232[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1231[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1230[zig_as_u32(16)];
static zig_u8 generator_growTree__anon_1229[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1227[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1226[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1225[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1224[zig_as_u32(50)];
static zig_u8 generator_fillOblateSpheroid__anon_1223[zig_as_u32(50)];
static zig_u8 generator_fillOblateSpheroid__anon_1222[zig_as_u32(50)];
static zig_u8 generator_fillOblateSpheroid__anon_1221[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1220[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1219[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1218[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1217[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1216[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1215[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1214[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1213[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1212[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1211[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1210[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1209[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1208[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1207[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1206[zig_as_u32(16)];
static zig_u8 generator_fillOblateSpheroid__anon_1205[zig_as_u32(50)];
static zig_u8 rand_Random_float__anon_695__anon_1204[zig_as_u32(16)];
static zig_u8 rand_Random_float__anon_695__anon_1203[zig_as_u32(16)];
static zig_u8 rand_Random_float__anon_695__anon_1202[zig_as_u32(16)];
static zig_u8 target_mips_cpu_mips32__anon_1172[zig_as_u32(7)];
static zig_u8 generator_create_tree__anon_746[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_745[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_744[zig_as_u32(50)];
static zig_u8 generator_create_tree__anon_743[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_742[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_741[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_740[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_739[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_738[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_737[zig_as_u32(16)];
static zig_u8 generator_create_tree__anon_736[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_735[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_734[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_733[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_732[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_731[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_730[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_729[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_728[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_727[zig_as_u32(16)];
static zig_u8 generator_create_mushrooms__anon_726[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_725[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_724[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_723[zig_as_u32(50)];
static zig_u8 generator_create_flowers__anon_722[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_721[zig_as_u32(50)];
static zig_u8 generator_create_flowers__anon_720[zig_as_u32(50)];
static zig_u8 generator_create_flowers__anon_719[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_718[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_717[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_716[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_715[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_714[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_713[zig_as_u32(16)];
static zig_u8 generator_create_flowers__anon_711[zig_as_u32(16)];
static zig_u8 generator_create_vein__anon_709[zig_as_u32(16)];
static zig_u8 generator_create_vein__anon_708[zig_as_u32(50)];
static zig_u8 generator_create_vein__anon_707[zig_as_u32(50)];
static zig_u8 generator_create_vein__anon_706[zig_as_u32(50)];
static zig_u8 generator_create_vein__anon_705[zig_as_u32(50)];
static zig_u8 generator_create_cave__anon_704[zig_as_u32(16)];
static zig_u8 generator_create_cave__anon_703[zig_as_u32(50)];
static zig_u8 generator_create_cave__anon_702[zig_as_u32(50)];
static zig_u8 generator_create_cave__anon_701[zig_as_u32(50)];
static zig_u8 generator_create_cave__anon_700[zig_as_u32(16)];
static zig_u8 generator_create_cave__anon_699[zig_as_u32(16)];
static zig_u8 generator_create_cave__anon_698[zig_as_u32(16)];
static zig_u8 generator_create_cave__anon_696[zig_as_u32(50)];
static zig_u8 generator_getIdx__anon_342[zig_as_u32(16)];
static zig_u8 generator_getIdx__anon_341[zig_as_u32(16)];
static zig_u8 generator_getIdx__anon_340[zig_as_u32(16)];
static zig_u8 generator_getIdx__anon_339[zig_as_u32(16)];
static zig_u8 generator_getIdx__anon_338[zig_as_u32(16)];
static zig_u8 perlin_onoise__anon_337[zig_as_u32(16)];
static zig_u8 generator_noise2__anon_336[zig_as_u32(16)];
static zig_u8 generator_noise2__anon_335[zig_as_u32(16)];
static zig_u8 generator_noise1__anon_334[zig_as_u32(16)];
static zig_u8 generator_noise1__anon_333[zig_as_u32(16)];
static zig_u8 generator_create_plants__anon_329[zig_as_u32(16)];
static zig_u8 generator_create_plants__anon_328[zig_as_u32(16)];
static zig_u8 generator_create_plants__anon_327[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_326[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_325[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_324[zig_as_u32(50)];
static zig_u8 generator_create_surface__anon_323[zig_as_u32(50)];
static zig_u8 generator_create_surface__anon_322[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_321[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_320[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_319[zig_as_u32(16)];
static zig_u8 generator_create_surface__anon_318[zig_as_u32(16)];
static zig_u8 generator_fill_lava__anon_317[zig_as_u32(16)];
static zig_u8 generator_fill_lava__anon_316[zig_as_u32(16)];
static zig_u8 generator_fill_lava__anon_315[zig_as_u32(16)];
static zig_u8 generator_fill_water__anon_314[zig_as_u32(16)];
static zig_u8 generator_fill_water__anon_313[zig_as_u32(16)];
static zig_u8 generator_fill_water__anon_312[zig_as_u32(16)];
static zig_u8 generator_fill_water__anon_311[zig_as_u32(50)];
static zig_u8 generator_fill_water__anon_310[zig_as_u32(16)];
static zig_u8 generator_fill_water__anon_309[zig_as_u32(16)];
static zig_u8 generator_make_ores__anon_308[zig_as_u32(16)];
static zig_u8 generator_make_ores__anon_307[zig_as_u32(16)];
static zig_u8 generator_make_ores__anon_306[zig_as_u32(16)];
static zig_u8 generator_make_caves__anon_305[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_304[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_303[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_302[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_301[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_300[zig_as_u32(50)];
static zig_u8 generator_create_strata__anon_299[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_298[zig_as_u32(16)];
static zig_u8 generator_create_strata__anon_297[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_296[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_295[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_294[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_293[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_292[zig_as_u32(50)];
static zig_u8 generator_smooth_heightmap__anon_291[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_290[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_289[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_288[zig_as_u32(16)];
static zig_u8 generator_smooth_heightmap__anon_287[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_286[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_285[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_284[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_283[zig_as_u32(50)];
static zig_u8 generator_generate_heightmap__anon_282[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_281[zig_as_u32(16)];
static zig_u8 generator_generate_heightmap__anon_276[zig_as_u32(16)];
static zig_u64 math_shr__anon_1457(zig_u64 const a0);
static zig_u64 math_shl__anon_1456(zig_u64 const a0);
static zig_bool math_isPowerOfTwo__anon_1455(zig_void);
static zig_u64 math_shr__anon_1454(zig_u64 const a0);
static zig_u64 math_shl__anon_1453(zig_u64 const a0);
static zig_bool math_isPowerOfTwo__anon_1449(zig_void);
static zig_u64 mem_readIntNative__anon_1448(zig_A_u8_8 const * const a0);
static zig_u64 math_rotl__anon_1445(zig_u64 const a0);
static zig_u64 math_rotl__anon_1444(zig_u64 const a0);
static zig_u8 mem_readIntNative__anon_1435(zig_A_u8_1 const * const a0);
static zig_u64 mem_readIntSliceNative__anon_1434(zig_L_u8 const a0);
static zig_u32 mem_readIntNative__anon_1433(zig_A_u8_4 const * const a0);
static zig_void rand_Random_init__anon_747_gen_fill(zig_void * const a0, zig_L_u8 const a1);
static zig_void debug_assert(zig_bool const a0);
static zig_u64 rand_Xoshiro256_next(zig_S_rand_Xoshiro256__255 * const a0);
static zig_f64 perlin_lerp(zig_f64 const a0, zig_f64 const a1, zig_f64 const a2);
static zig_usize perlin_permutation[zig_as_u32(512)];
static zig_f64 perlin_fade(zig_f64 const a0);
static zig_usize generator_getIdx(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2);
static zig_u8 * generator_worldData;
static zig_bool generator_isSpaceForTree(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2);
static zig_u32 mem_readIntSliceNative__anon_1200(zig_L_u8 const a0);
static zig_void target_Target_Cpu_Feature_Set_addFeature(zig_S_target_Target_Cpu_Feature_Set__1123 * const a0, zig_u16 const a1);
static zig_S_target_Target_Cpu_Feature_Set__1123 target_Target_Cpu_Feature_Set_empty_workaround(zig_void);
static zig_S_target_Target_Cpu_Model__1116 target_mips_cpu_mips32;
static zig_S_target_Target_Cpu__1087 builtin_cpu;
static zig_u8 target_Target_Cpu_Arch_endian(zig_u8 const a0);
static zig_u8 mem_native_endian;
static zig_S_target_Target_Cpu_Feature_Set__1123 target_Target_Cpu_Feature_feature_set_fns_28target_mips_Feature_29_featureSet(zig_L_target_mips_Feature const a0);
static zig_void rand_Random_bytes(zig_S_rand_Random__343 const a0, zig_L_u8 const a1);
static zig_S_rand_Random__343 rand_Random_init__anon_747(zig_S_rand_Xoshiro256__255 * const a0);
static zig_void rand_Xoshiro256_fill(zig_S_rand_Xoshiro256__255 * const a0, zig_L_u8 const a1);
zig_extern zig_f64 grad(zig_usize const a0, zig_f64 const a1, zig_f64 const a2, zig_f64 const a3);
static zig_f64 perlin_noise(zig_f64 const a0, zig_f64 const a1, zig_f64 const a2);
static zig_usize rand_Random_int__anon_712(zig_S_rand_Random__343 const a0);
static zig_u8 mem_readIntSliceNative__anon_1228(zig_L_u8 const a0);
static zig_u8 rand_Random_int__anon_710(zig_S_rand_Random__343 const a0);
static zig_i32 rand_Random_int__anon_697(zig_S_rand_Random__343 const a0);
static zig_u64 rand_Random_int__anon_1201(zig_S_rand_Random__343 const a0);
static zig_u32 rand_Random_int__anon_448(zig_S_rand_Random__343 const a0);
static zig_f32 rand_Random_float__anon_695(zig_S_rand_Random__343 const a0);
static zig_f64 perlin_pnoise(zig_f64 const a0, zig_f64 const a1, zig_u32 const a2);
static zig_S_rand_Xoshiro256__255 generator_rnd;
static zig_S_rand_Random__343 rand_Xoshiro256_random(zig_S_rand_Xoshiro256__255 * const a0);
static zig_bool generator_growTree(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2, zig_u32 const a3);
static zig_i32 generator_heightMap[zig_as_u32(65536)];
static zig_void generator_create_tree(zig_void);
static zig_void generator_create_flowers(zig_void);
static zig_void generator_fillOblateSpheroid(zig_i32 const a0, zig_i32 const a1, zig_i32 const a2, zig_f32 const a3, zig_u8 const a4);
static zig_void generator_create_vein(zig_f32 const a0, zig_u8 const a1);
static zig_void generator_create_cave(zig_void);
static zig_i32 generator_waterLevel;
static zig_void generator_create_mushrooms(zig_void);
static zig_u64 builtin_zig_backend;
static zig_cold zig_noreturn builtin_default_panic(zig_L_u8 const a0, zig_S_builtin_StackTrace__277 * const a1, zig_Q_usize const a2);
static zig_f64 perlin_onoise(zig_usize const a0, zig_f64 const a1, zig_f64 const a2, zig_u32 const a3);
static zig_u32 generator_map_seed;
static zig_f64 generator_noise2(zig_f32 const a0, zig_f32 const a1);
static zig_void generator_create_plants(zig_void);
static zig_void generator_create_surface(zig_void);
static zig_void generator_fill_lava(zig_void);
static zig_void generator_fill_water(zig_void);
static zig_void generator_make_ores(zig_void);
static zig_void generator_make_caves(zig_void);
static zig_void generator_create_strata(zig_void);
static zig_f64 generator_noise1(zig_f32 const a0, zig_f32 const a1);
static zig_void generator_smooth_heightmap(zig_void);
static zig_S_rand_SplitMix64__330 rand_SplitMix64_init(zig_u64 const a0);
static zig_u64 rand_SplitMix64_next(zig_S_rand_SplitMix64__330 * const a0);
static zig_void rand_Xoshiro256_seed(zig_S_rand_Xoshiro256__255 * const a0, zig_u64 const a1);
static zig_S_rand_Xoshiro256__255 rand_Xoshiro256_init(zig_u64 const a0);
static zig_void generator_generate_heightmap(zig_void);
zig_extern zig_void generate(zig_u32 const a0, zig_u8 * const a1);
static zig_u8 builtin_output_mode;
static zig_u64 builtin_zig_backend = zig_as_u64(3);
static zig_u8 builtin_output_mode = 2;

zig_void generate(zig_u32 const a0, zig_u8 * const a1) {
 /* file:2:5 */
 (*(zig_u32 * )((zig_u32 * )&generator_map_seed)) = a0;
 /* file:3:5 */
 (*(zig_u8 * * )((zig_u8 * * )&generator_worldData)) = a1;
 /* file:5:5 */
 /* file:5:22 */
 zig_u64 const t0 = (zig_u64 )a0;
 zig_S_rand_Xoshiro256__255 const t1 = rand_Xoshiro256_init(t0);
 (*(zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd)) = t1;
 /* file:8:5 */
 /* file:8:23 */
 generator_generate_heightmap();
 /* file:10:5 */
 /* file:10:21 */
 generator_smooth_heightmap();
 /* file:12:5 */
 /* file:12:18 */
 generator_create_strata();
 /* file:15:5 */
 /* file:15:15 */
 generator_make_caves();
 /* file:17:5 */
 /* file:17:14 */
 generator_make_ores();
 /* file:20:5 */
 /* file:20:15 */
 generator_fill_water();
 /* file:23:5 */
 /* file:23:14 */
 generator_fill_lava();
 /* file:26:5 */
 /* file:26:19 */
 generator_create_surface();
 /* file:29:5 */
 /* file:29:18 */
 generator_create_plants();
 return;
}
static zig_u32 generator_map_seed = zig_as_u32(0);
static zig_u8 * generator_worldData = ((zig_u8 * )zig_as_u32(0xaaaaaaaa));
static zig_S_rand_Xoshiro256__255 generator_rnd = {{zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa)}};

static zig_S_rand_Xoshiro256__255 rand_Xoshiro256_init(zig_u64 const a0) {
 /* file:2:5 */
 zig_S_rand_Xoshiro256__255 t0;
 zig_S_rand_Xoshiro256__255 * const t1 = (zig_S_rand_Xoshiro256__255 * )&t0;
 (*t1) = (zig_S_rand_Xoshiro256__255 ){{zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa), zig_as_u64(0xaaaaaaaaaaaaaaaa)}};
 /* var:x */
 /* file:6:5 */
 /* file:6:11 */
 rand_Xoshiro256_seed(&t0, a0);
 /* file:7:5 */
 zig_S_rand_Xoshiro256__255 const t2 = t0;
 /* file:7:5 */
 return t2;
}

static zig_void generator_generate_heightmap(zig_void) {
 /* file:3:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:4:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:4:31 */
     /* file:6:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:7:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:7:31 */
         /* file:9:5 */
         zig_f32 t8;
         zig_usize const t9 = t4;
         zig_f32 const t10 = __floatunsisf(t9);
         zig_f32 * const t11 = (zig_f32 * )&t8;
         (*t11) = t10;
         /* var:xf */
         /* file:10:5 */
         zig_f32 t12;
         zig_usize const t13 = t0;
         zig_f32 const t14 = __floatunsisf(t13);
         zig_f32 * const t15 = (zig_f32 * )&t12;
         (*t15) = t14;
         /* var:zf */
         /* file:12:5 */
         zig_f64 t16;
         /* file:12:27 */
         zig_f32 const t17 = t8;
         zig_f32 const t18 = zig_mul_f32(t17, (zig_f32 )zig_as_f32(0x1.4cccccp0, zig_as_i32(0x3fa66666)));
         zig_f32 const t19 = t12;
         zig_f32 const t20 = zig_mul_f32(t19, (zig_f32 )zig_as_f32(0x1.4cccccp0, zig_as_i32(0x3fa66666)));
         zig_f64 const t21 = generator_noise1(t18, t20);
         zig_f64 const t22 = zig_div_f64(t21, (zig_f64 )zig_as_f64(0x1.8p2, zig_as_i64(0x4018000000000000)));
         zig_f64 const t23 = zig_sub_f64(t22, (zig_f64 )zig_as_f64(0x1p2, zig_as_i64(0x4010000000000000)));
         zig_f64 * const t24 = (zig_f64 * )&t16;
         (*t24) = t23;
         /* var:heightLow */
         /* file:13:5 */
         zig_f64 t25;
         /* file:13:28 */
         zig_f32 const t26 = t8;
         zig_f32 const t27 = zig_mul_f32(t26, (zig_f32 )zig_as_f32(0x1.4cccccp0, zig_as_i32(0x3fa66666)));
         zig_f32 const t28 = t12;
         zig_f32 const t29 = zig_mul_f32(t28, (zig_f32 )zig_as_f32(0x1.4cccccp0, zig_as_i32(0x3fa66666)));
         zig_f64 const t30 = generator_noise2(t27, t29);
         zig_f64 const t31 = zig_div_f64(t30, (zig_f64 )zig_as_f64(0x1.4p2, zig_as_i64(0x4014000000000000)));
         zig_f64 const t32 = zig_add_f64(t31, (zig_f64 )zig_as_f64(0x1.8p2, zig_as_i64(0x4018000000000000)));
         zig_f64 * const t33 = (zig_f64 * )&t25;
         (*t33) = t32;
         /* var:heightHigh */
         /* file:15:5 */
         zig_f64 t34;
         t34 = (zig_f64 )zig_as_f64(0x0.0p0, zig_as_i64(0x0));
         /* var:heightResult */
         /* file:17:8 */
         {
          /* file:17:21 */
          zig_f32 const t35 = t8;
          zig_f32 const t36 = t12;
          zig_u32 const t37 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
          zig_T_tuple_7bu32_2c_20u1_7d t38;
          t38.f1 = zig_addo_u32(&t38.f0, t37, zig_as_u32(5), zig_as_u8(32));
          zig_u8 const t39 = t38.f1;
          zig_bool const t40 = t39 == zig_as_u8(0);
          {
           if (t40) {
            goto zig_block_5;
           } else {
            builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_276), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
           }
          }
          zig_block_5:;
          zig_u32 const t41 = t38.f0;
          zig_f64 const t42 = __extendsfdf2(t35);
          zig_f64 const t43 = __extendsfdf2(t36);
          zig_f64 const t44 = perlin_onoise(zig_as_u32(6), t42, t43, t41);
          zig_f64 const t45 = zig_div_f64(t44, (zig_f64 )zig_as_f64(0x1p3, zig_as_i64(0x4020000000000000)));
          zig_bool const t46 = zig_gt_f64(t45, (zig_f64 )zig_as_f64(0x0.0p0, zig_as_i64(0x0))) > zig_as_i8(0);
          if (t46) {
           /* file:18:9 */
           zig_f64 const t47 = t16;
           t34 = t47;
           goto zig_block_4;
          } else {
           /* file:20:28 */
           {
            zig_f64 const t48 = t25;
            zig_f64 const t49 = t16;
            zig_bool const t50 = zig_gt_f64(t48, t49) > zig_as_i8(0);
            if (t50) {
             zig_f64 const t51 = t25;
             t34 = t51;
             goto zig_block_6;
            } else {
             zig_f64 const t52 = t16;
             t34 = t52;
             goto zig_block_6;
            }
           }
           zig_block_6:;
           goto zig_block_4;
          }
         }
         zig_block_4:;
         /* file:23:5 */
         zig_f64 const t53 = t34;
         zig_f64 const t54 = zig_div_f64(t53, (zig_f64 )zig_as_f64(0x1p1, zig_as_i64(0x4000000000000000)));
         t34 = t54;
         /* file:25:8 */
         {
          zig_f64 const t55 = t34;
          zig_bool const t56 = zig_lt_f64(t55, (zig_f64 )zig_as_f64(0x0.0p0, zig_as_i64(0x0))) < zig_as_i8(0);
          if (t56) {
           /* file:26:9 */
           zig_f64 const t57 = t34;
           zig_f64 const t58 = zig_mul_f64(t57, (zig_f64 )zig_as_f64(0x1.999999999999ap-1, zig_as_i64(0x3fe999999999999a)));
           t34 = t58;
           goto zig_block_7;
          } else {
           goto zig_block_7;
          }
         }
         zig_block_7:;
         /* file:28:5 */
         zig_usize const t59 = t4;
         zig_usize const t60 = t0;
         zig_T_tuple_7busize_2c_20u1_7d t61;
         t61.f1 = zig_mulo_u32(&t61.f0, t60, zig_as_u32(256), zig_as_u8(32));
         zig_u8 const t62 = t61.f1;
         zig_bool const t63 = t62 == zig_as_u8(0);
         {
          if (t63) {
           goto zig_block_8;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_281), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_8:;
         zig_usize const t64 = t61.f0;
         zig_T_tuple_7busize_2c_20u1_7d t65;
         t65.f1 = zig_addo_u32(&t65.f0, t59, t64, zig_as_u8(32));
         zig_u8 const t66 = t65.f1;
         zig_bool const t67 = t66 == zig_as_u8(0);
         {
          if (t67) {
           goto zig_block_9;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_282), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_9:;
         zig_usize const t68 = t65.f0;
         zig_bool const t69 = t68 < zig_as_u32(65536);
         {
          if (t69) {
           goto zig_block_10;
          } else {
           zig_breakpoint();
           zig_unreachable();
          }
         }
         zig_block_10:;
         zig_i32 * const t70 = &((*(zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap)))[t68];
         zig_f64 const t71 = t34;
         zig_i32 const t72 = zig_wrap_i32(__fixdfsi(t71), zig_as_u8(32));
         zig_f64 const t73 = __floatsidf(t72);
         zig_f64 const t74 = zig_sub_f64(t71, t73);
         zig_bool const t75 = zig_lt_f64(t74, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000))) < zig_as_i8(0);
         zig_bool const t76 = zig_gt_f64(t74, (zig_f64 )zig_as_f64(-0x1p0, -zig_as_i64(0x4010000000000000))) > zig_as_i8(0);
         zig_bool const t77 = t75 & t76;
         {
          if (t77) {
           goto zig_block_11;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_283), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_11:;
         zig_T_tuple_7bi32_2c_20u1_7d t78;
         t78.f1 = zig_addo_i32(&t78.f0, zig_as_i32(32), t72, zig_as_u8(32));
         zig_u8 const t79 = t78.f1;
         zig_bool const t80 = t79 == zig_as_u8(0);
         {
          if (t80) {
           goto zig_block_12;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_284), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_12:;
         zig_i32 const t81 = t78.f0;
         (*t70) = t81;
         /* file:7:23 */
         zig_usize const t82 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t83;
         t83.f1 = zig_addo_u32(&t83.f0, t82, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t84 = t83.f1;
         zig_bool const t85 = t84 == zig_as_u8(0);
         {
          if (t85) {
           goto zig_block_13;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_285), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_13:;
         zig_usize const t86 = t83.f0;
         t4 = t86;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:4:23 */
     zig_usize const t87 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t88;
     t88.f1 = zig_addo_u32(&t88.f0, t87, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t89 = t88.f1;
     zig_bool const t90 = t89 == zig_as_u8(0);
     {
      if (t90) {
       goto zig_block_14;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_generate_heightmap__anon_286), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_14:;
     zig_usize const t91 = t88.f0;
     t0 = t91;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_smooth_heightmap(zig_void) {
 /* file:2:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:3:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:3:31 */
     /* file:5:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:6:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:6:31 */
         /* file:8:5 */
         zig_f32 t8;
         zig_usize const t9 = t4;
         zig_f32 const t10 = __floatunsisf(t9);
         zig_f32 * const t11 = (zig_f32 * )&t8;
         (*t11) = t10;
         /* var:xf */
         /* file:9:5 */
         zig_f32 t12;
         zig_usize const t13 = t0;
         zig_f32 const t14 = __floatunsisf(t13);
         zig_f32 * const t15 = (zig_f32 * )&t12;
         (*t15) = t14;
         /* var:zf */
         /* file:11:5 */
         zig_f64 t16;
         /* file:11:19 */
         zig_f32 const t17 = t8;
         zig_f32 const t18 = zig_mul_f32(t17, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
         zig_f32 const t19 = t12;
         zig_f32 const t20 = zig_mul_f32(t19, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
         zig_f64 const t21 = generator_noise1(t18, t20);
         zig_f64 const t22 = zig_div_f64(t21, (zig_f64 )zig_as_f64(0x1p3, zig_as_i64(0x4020000000000000)));
         zig_f64 * const t23 = (zig_f64 * )&t16;
         (*t23) = t22;
         /* var:a */
         /* file:12:5 */
         zig_i32 t24;
         {
          /* file:12:22 */
          /* file:12:28 */
          zig_f32 const t25 = t8;
          zig_f32 const t26 = zig_mul_f32(t25, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
          zig_f32 const t27 = t12;
          zig_f32 const t28 = zig_mul_f32(t27, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
          zig_f64 const t29 = generator_noise2(t26, t28);
          zig_bool const t30 = zig_gt_f64(t29, (zig_f64 )zig_as_f64(0x0.0p0, zig_as_i64(0x0))) > zig_as_i8(0);
          if (t30) {
           t24 = zig_as_i32(1);
           goto zig_block_4;
          } else {
           t24 = zig_as_i32(0);
           goto zig_block_4;
          }
         }
         zig_block_4:;
         /* var:b */
         /* file:14:8 */
         {
          zig_f64 const t31 = t16;
          zig_bool const t32 = zig_gt_f64(t31, (zig_f64 )zig_as_f64(0x1p1, zig_as_i64(0x4000000000000000))) > zig_as_i8(0);
          if (t32) {
           /* file:15:9 */
           zig_usize const t33 = t4;
           zig_usize const t34 = t0;
           zig_T_tuple_7busize_2c_20u1_7d t35;
           t35.f1 = zig_mulo_u32(&t35.f0, t34, zig_as_u32(256), zig_as_u8(32));
           zig_u8 const t36 = t35.f1;
           zig_bool const t37 = t36 == zig_as_u8(0);
           {
            if (t37) {
             goto zig_block_6;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_287), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_6:;
           zig_usize const t38 = t35.f0;
           zig_T_tuple_7busize_2c_20u1_7d t39;
           t39.f1 = zig_addo_u32(&t39.f0, t33, t38, zig_as_u8(32));
           zig_u8 const t40 = t39.f1;
           zig_bool const t41 = t40 == zig_as_u8(0);
           {
            if (t41) {
             goto zig_block_7;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_288), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_7:;
           zig_usize const t42 = t39.f0;
           zig_bool const t43 = t42 < zig_as_u32(65536);
           {
            if (t43) {
             goto zig_block_8;
            } else {
             zig_breakpoint();
             zig_unreachable();
            }
           }
           zig_block_8:;
           zig_i32 * const t44 = &((*(zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap)))[t42];
           zig_i32 t45[zig_as_u32(65536)];
           memcpy(t45, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
           zig_usize const t46 = t4;
           zig_usize const t47 = t0;
           zig_T_tuple_7busize_2c_20u1_7d t48;
           t48.f1 = zig_mulo_u32(&t48.f0, t47, zig_as_u32(256), zig_as_u8(32));
           zig_u8 const t49 = t48.f1;
           zig_bool const t50 = t49 == zig_as_u8(0);
           {
            if (t50) {
             goto zig_block_9;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_289), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_9:;
           zig_usize const t51 = t48.f0;
           zig_T_tuple_7busize_2c_20u1_7d t52;
           t52.f1 = zig_addo_u32(&t52.f0, t46, t51, zig_as_u8(32));
           zig_u8 const t53 = t52.f1;
           zig_bool const t54 = t53 == zig_as_u8(0);
           {
            if (t54) {
             goto zig_block_10;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_290), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_10:;
           zig_usize const t55 = t52.f0;
           zig_bool const t56 = t55 < zig_as_u32(65536);
           {
            if (t56) {
             goto zig_block_11;
            } else {
             zig_breakpoint();
             zig_unreachable();
            }
           }
           zig_block_11:;
           zig_i32 const t57 = t45[t55];
           zig_i32 const t58 = t24;
           zig_T_tuple_7bi32_2c_20u1_7d t59;
           t59.f1 = zig_subo_i32(&t59.f0, t57, t58, zig_as_u8(32));
           zig_u8 const t60 = t59.f1;
           zig_bool const t61 = t60 == zig_as_u8(0);
           {
            if (t61) {
             goto zig_block_12;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_291), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_12:;
           zig_i32 const t62 = t59.f0;
           zig_f32 const t63 = __floatsisf(t62);
           zig_f32 const t64 = zig_div_f32(t63, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
           zig_i32 const t65 = zig_wrap_i32(__fixsfsi(t64), zig_as_u8(32));
           zig_f32 const t66 = __floatsisf(t65);
           zig_f32 const t67 = zig_sub_f32(t64, t66);
           zig_bool const t68 = zig_lt_f32(t67, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
           zig_bool const t69 = zig_gt_f32(t67, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
           zig_bool const t70 = t68 & t69;
           {
            if (t70) {
             goto zig_block_13;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_292), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_13:;
           zig_T_tuple_7bi32_2c_20u1_7d t71;
           t71.f1 = zig_mulo_i32(&t71.f0, t65, zig_as_i32(2), zig_as_u8(32));
           zig_u8 const t72 = t71.f1;
           zig_bool const t73 = t72 == zig_as_u8(0);
           {
            if (t73) {
             goto zig_block_14;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_293), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_14:;
           zig_i32 const t74 = t71.f0;
           zig_i32 const t75 = t24;
           zig_T_tuple_7bi32_2c_20u1_7d t76;
           t76.f1 = zig_addo_i32(&t76.f0, t74, t75, zig_as_u8(32));
           zig_u8 const t77 = t76.f1;
           zig_bool const t78 = t77 == zig_as_u8(0);
           {
            if (t78) {
             goto zig_block_15;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_294), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_15:;
           zig_i32 const t79 = t76.f0;
           (*t44) = t79;
           goto zig_block_5;
          } else {
           goto zig_block_5;
          }
         }
         zig_block_5:;
         /* file:6:23 */
         zig_usize const t80 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t81;
         t81.f1 = zig_addo_u32(&t81.f0, t80, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t82 = t81.f1;
         zig_bool const t83 = t82 == zig_as_u8(0);
         {
          if (t83) {
           goto zig_block_16;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_295), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_16:;
         zig_usize const t84 = t81.f0;
         t4 = t84;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:3:23 */
     zig_usize const t85 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t86;
     t86.f1 = zig_addo_u32(&t86.f0, t85, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t87 = t86.f1;
     zig_bool const t88 = t87 == zig_as_u8(0);
     {
      if (t88) {
       goto zig_block_17;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_smooth_heightmap__anon_296), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_17:;
     zig_usize const t89 = t86.f0;
     t0 = t89;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_create_strata(zig_void) {
 /* file:3:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:4:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:4:31 */
     /* file:6:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:7:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:7:31 */
         /* file:9:5 */
         zig_f64 t8;
         /* file:9:38 */
         zig_usize const t9 = t4;
         zig_f32 const t10 = __floatunsisf(t9);
         zig_usize const t11 = t0;
         zig_f32 const t12 = __floatunsisf(t11);
         zig_u32 const t13 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
         zig_T_tuple_7bu32_2c_20u1_7d t14;
         t14.f1 = zig_addo_u32(&t14.f0, t13, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t15 = t14.f1;
         zig_bool const t16 = t15 == zig_as_u8(0);
         {
          if (t16) {
           goto zig_block_4;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_297), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_4:;
         zig_u32 const t17 = t14.f0;
         zig_f64 const t18 = __extendsfdf2(t10);
         zig_f64 const t19 = __extendsfdf2(t12);
         zig_f64 const t20 = perlin_onoise(zig_as_u32(8), t18, t19, t17);
         zig_f64 const t21 = zig_div_f64(t20, (zig_f64 )zig_as_f64(0x1.8p4, zig_as_i64(0x4038000000000000)));
         zig_f64 const t22 = zig_sub_f64(t21, (zig_f64 )zig_as_f64(0x1p2, zig_as_i64(0x4010000000000000)));
         zig_f64 * const t23 = (zig_f64 * )&t8;
         (*t23) = t22;
         /* var:dirtThickness */
         /* file:10:5 */
         zig_i32 t24;
         zig_i32 t25[zig_as_u32(65536)];
         memcpy(t25, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
         zig_usize const t26 = t4;
         zig_usize const t27 = t0;
         zig_T_tuple_7busize_2c_20u1_7d t28;
         t28.f1 = zig_mulo_u32(&t28.f0, t27, zig_as_u32(256), zig_as_u8(32));
         zig_u8 const t29 = t28.f1;
         zig_bool const t30 = t29 == zig_as_u8(0);
         {
          if (t30) {
           goto zig_block_5;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_298), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_5:;
         zig_usize const t31 = t28.f0;
         zig_T_tuple_7busize_2c_20u1_7d t32;
         t32.f1 = zig_addo_u32(&t32.f0, t26, t31, zig_as_u8(32));
         zig_u8 const t33 = t32.f1;
         zig_bool const t34 = t33 == zig_as_u8(0);
         {
          if (t34) {
           goto zig_block_6;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_299), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_6:;
         zig_usize const t35 = t32.f0;
         zig_bool const t36 = t35 < zig_as_u32(65536);
         {
          if (t36) {
           goto zig_block_7;
          } else {
           zig_breakpoint();
           zig_unreachable();
          }
         }
         zig_block_7:;
         zig_i32 const t37 = t25[t35];
         zig_i32 * const t38 = (zig_i32 * )&t24;
         (*t38) = t37;
         /* var:dirtTransition */
         /* file:11:5 */
         zig_i32 t39;
         zig_i32 const t40 = t24;
         zig_f64 const t41 = t8;
         zig_i32 const t42 = zig_wrap_i32(__fixdfsi(t41), zig_as_u8(32));
         zig_f64 const t43 = __floatsidf(t42);
         zig_f64 const t44 = zig_sub_f64(t41, t43);
         zig_bool const t45 = zig_lt_f64(t44, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000))) < zig_as_i8(0);
         zig_bool const t46 = zig_gt_f64(t44, (zig_f64 )zig_as_f64(-0x1p0, -zig_as_i64(0x4010000000000000))) > zig_as_i8(0);
         zig_bool const t47 = t45 & t46;
         {
          if (t47) {
           goto zig_block_8;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_300), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_8:;
         zig_T_tuple_7bi32_2c_20u1_7d t48;
         t48.f1 = zig_addo_i32(&t48.f0, t40, t42, zig_as_u8(32));
         zig_u8 const t49 = t48.f1;
         zig_bool const t50 = t49 == zig_as_u8(0);
         {
          if (t50) {
           goto zig_block_9;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_301), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_9:;
         zig_i32 const t51 = t48.f0;
         zig_i32 * const t52 = (zig_i32 * )&t39;
         (*t52) = t51;
         /* var:stoneTransition */
         /* file:13:5 */
         zig_usize t53;
         t53 = zig_as_u32(0);
         /* var:y */
         {
          while (zig_true) {
           {
            /* file:14:11 */
            zig_usize const t54 = t53;
            zig_u32 t55;
            memcpy(&t55, &t54, sizeof(zig_u32 ));
            t55 = zig_wrap_u32(t55, zig_as_u8(32));
            zig_bool const t56 = t55 < zig_as_u32(64);
            if (t56) {
             /* file:14:30 */
             /* file:15:9 */
             zig_u8 t57;
             t57 = zig_as_u8(0);
             /* var:bType */
             /* file:17:12 */
             {
              zig_usize const t58 = t53;
              zig_u32 t59;
              memcpy(&t59, &t58, sizeof(zig_u32 ));
              t59 = zig_wrap_u32(t59, zig_as_u8(32));
              zig_bool const t60 = t59 == zig_as_u32(0);
              if (t60) {
               /* file:18:13 */
               t57 = zig_as_u8(10);
               goto zig_block_12;
              } else {
               {
                /* file:19:19 */
                zig_usize const t61 = t53;
                zig_i32 const t62 = t39;
                zig_i64 const t63 = (zig_i64 )t61;
                zig_i64 const t64 = (zig_i64 )t62;
                zig_bool const t65 = t63 <= t64;
                if (t65) {
                 /* file:20:13 */
                 t57 = zig_as_u8(1);
                 goto zig_block_13;
                } else {
                 {
                  /* file:21:19 */
                  zig_usize const t66 = t53;
                  zig_i32 const t67 = t24;
                  zig_i64 const t68 = (zig_i64 )t66;
                  zig_i64 const t69 = (zig_i64 )t67;
                  zig_bool const t70 = t68 <= t69;
                  if (t70) {
                   /* file:22:13 */
                   t57 = zig_as_u8(3);
                   goto zig_block_14;
                  } else {
                   goto zig_block_14;
                  }
                 }
                 zig_block_14:;
                 goto zig_block_13;
                }
               }
               zig_block_13:;
               goto zig_block_12;
              }
             }
             zig_block_12:;
             /* file:25:9 */
             /* file:25:25 */
             zig_usize const t71 = t4;
             zig_u32 const t72 = (zig_u32 )t71;
             zig_usize const t73 = t53;
             zig_u32 const t74 = (zig_u32 )t73;
             zig_usize const t75 = t0;
             zig_u32 const t76 = (zig_u32 )t75;
             zig_usize const t77 = generator_getIdx(t72, t74, t76);
             zig_u8 * const t78 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t79 = &(t78)[t77];
             zig_u8 const t80 = t57;
             (*t79) = t80;
             /* file:14:22 */
             zig_usize const t81 = t53;
             zig_T_tuple_7busize_2c_20u1_7d t82;
             t82.f1 = zig_addo_u32(&t82.f0, t81, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t83 = t82.f1;
             zig_bool const t84 = t83 == zig_as_u8(0);
             {
              if (t84) {
               goto zig_block_15;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_302), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_15:;
             zig_usize const t85 = t82.f0;
             t53 = t85;
             goto zig_block_11;
            } else {
             goto zig_block_10;
            }
           }
           zig_block_11:;
          }
         }
         zig_block_10:;
         /* file:7:23 */
         zig_usize const t86 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t87;
         t87.f1 = zig_addo_u32(&t87.f0, t86, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t88 = t87.f1;
         zig_bool const t89 = t88 == zig_as_u8(0);
         {
          if (t89) {
           goto zig_block_16;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_303), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_16:;
         zig_usize const t90 = t87.f0;
         t4 = t90;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:4:23 */
     zig_usize const t91 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t92;
     t92.f1 = zig_addo_u32(&t92.f0, t91, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t93 = t92.f1;
     zig_bool const t94 = t93 == zig_as_u8(0);
     {
      if (t94) {
       goto zig_block_17;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_strata__anon_304), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_17:;
     zig_usize const t95 = t92.f0;
     t0 = t95;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_make_caves(zig_void) {
 /* file:2:5 */
 zig_usize t0;
 t0 = zig_as_u32(512);
 /* var:numCaves */
 /* file:4:5 */
 zig_usize t1;
 t1 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:5:11 */
    zig_usize const t2 = t1;
    zig_usize const t3 = t0;
    zig_u32 t4;
    memcpy(&t4, &t2, sizeof(zig_u32 ));
    t4 = zig_wrap_u32(t4, zig_as_u8(32));
    zig_u32 t5;
    memcpy(&t5, &t3, sizeof(zig_u32 ));
    t5 = zig_wrap_u32(t5, zig_as_u8(32));
    zig_bool const t6 = t4 < t5;
    if (t6) {
     /* file:5:36 */
     /* file:6:9 */
     /* file:6:20 */
     generator_create_cave();
     /* file:5:28 */
     zig_usize const t7 = t1;
     zig_T_tuple_7busize_2c_20u1_7d t8;
     t8.f1 = zig_addo_u32(&t8.f0, t7, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t9 = t8.f1;
     zig_bool const t10 = t9 == zig_as_u8(0);
     {
      if (t10) {
       goto zig_block_2;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_make_caves__anon_305), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_2:;
     zig_usize const t11 = t8.f0;
     t1 = t11;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_make_ores(zig_void) {
 /* file:2:5 */
 zig_usize t0;
 zig_usize * const t1 = (zig_usize * )&t0;
 (*t1) = zig_as_u32(230);
 /* var:numCoal */
 /* file:3:5 */
 zig_usize t2;
 zig_usize * const t3 = (zig_usize * )&t2;
 (*t3) = zig_as_u32(179);
 /* var:numIron */
 /* file:4:5 */
 zig_usize t4;
 zig_usize * const t5 = (zig_usize * )&t4;
 (*t5) = zig_as_u32(128);
 /* var:numGold */
 /* file:6:5 */
 zig_usize t6;
 t6 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:7:11 */
    zig_usize const t7 = t6;
    zig_usize const t8 = t0;
    zig_u32 t9;
    memcpy(&t9, &t7, sizeof(zig_u32 ));
    t9 = zig_wrap_u32(t9, zig_as_u8(32));
    zig_u32 t10;
    memcpy(&t10, &t8, sizeof(zig_u32 ));
    t10 = zig_wrap_u32(t10, zig_as_u8(32));
    zig_bool const t11 = t9 < t10;
    if (t11) {
     /* file:7:35 */
     /* file:8:9 */
     /* file:8:20 */
     generator_create_vein((zig_f32 )zig_as_f32(0x1.ccccccp-1, zig_as_i32(0x3f666666)), zig_as_u8(16));
     /* file:7:27 */
     zig_usize const t12 = t6;
     zig_T_tuple_7busize_2c_20u1_7d t13;
     t13.f1 = zig_addo_u32(&t13.f0, t12, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t14 = t13.f1;
     zig_bool const t15 = t14 == zig_as_u8(0);
     {
      if (t15) {
       goto zig_block_2;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_make_ores__anon_306), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_2:;
     zig_usize const t16 = t13.f0;
     t6 = t16;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 /* file:11:5 */
 t6 = zig_as_u32(0);
 {
  while (zig_true) {
   {
    /* file:12:11 */
    zig_usize const t17 = t6;
    zig_usize const t18 = t2;
    zig_u32 t19;
    memcpy(&t19, &t17, sizeof(zig_u32 ));
    t19 = zig_wrap_u32(t19, zig_as_u8(32));
    zig_u32 t20;
    memcpy(&t20, &t18, sizeof(zig_u32 ));
    t20 = zig_wrap_u32(t20, zig_as_u8(32));
    zig_bool const t21 = t19 < t20;
    if (t21) {
     /* file:12:35 */
     /* file:13:9 */
     /* file:13:20 */
     generator_create_vein((zig_f32 )zig_as_f32(0x1.666666p-1, zig_as_i32(0x3f333333)), zig_as_u8(15));
     /* file:12:27 */
     zig_usize const t22 = t6;
     zig_T_tuple_7busize_2c_20u1_7d t23;
     t23.f1 = zig_addo_u32(&t23.f0, t22, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t24 = t23.f1;
     zig_bool const t25 = t24 == zig_as_u8(0);
     {
      if (t25) {
       goto zig_block_5;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_make_ores__anon_307), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_5:;
     zig_usize const t26 = t23.f0;
     t6 = t26;
     goto zig_block_4;
    } else {
     goto zig_block_3;
    }
   }
   zig_block_4:;
  }
 }
 zig_block_3:;
 /* file:16:5 */
 t6 = zig_as_u32(0);
 {
  while (zig_true) {
   {
    /* file:17:11 */
    zig_usize const t27 = t6;
    zig_usize const t28 = t4;
    zig_u32 t29;
    memcpy(&t29, &t27, sizeof(zig_u32 ));
    t29 = zig_wrap_u32(t29, zig_as_u8(32));
    zig_u32 t30;
    memcpy(&t30, &t28, sizeof(zig_u32 ));
    t30 = zig_wrap_u32(t30, zig_as_u8(32));
    zig_bool const t31 = t29 < t30;
    if (t31) {
     /* file:17:35 */
     /* file:18:9 */
     /* file:18:20 */
     generator_create_vein((zig_f32 )zig_as_f32(0x1p-1, zig_as_i32(0x3f000000)), zig_as_u8(14));
     /* file:17:27 */
     zig_usize const t32 = t6;
     zig_T_tuple_7busize_2c_20u1_7d t33;
     t33.f1 = zig_addo_u32(&t33.f0, t32, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t34 = t33.f1;
     zig_bool const t35 = t34 == zig_as_u8(0);
     {
      if (t35) {
       goto zig_block_8;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_make_ores__anon_308), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_8:;
     zig_usize const t36 = t33.f0;
     t6 = t36;
     goto zig_block_7;
    } else {
     goto zig_block_6;
    }
   }
   zig_block_7:;
  }
 }
 zig_block_6:;
 return;
}

static zig_void generator_fill_water(zig_void) {
 /* file:3:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:4:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:4:31 */
     /* file:6:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:7:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:7:31 */
         /* file:9:5 */
         zig_usize t8;
         zig_i32 t9[zig_as_u32(65536)];
         memcpy(t9, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
         zig_usize const t10 = t4;
         zig_usize const t11 = t0;
         zig_T_tuple_7busize_2c_20u1_7d t12;
         t12.f1 = zig_mulo_u32(&t12.f0, t11, zig_as_u32(256), zig_as_u8(32));
         zig_u8 const t13 = t12.f1;
         zig_bool const t14 = t13 == zig_as_u8(0);
         {
          if (t14) {
           goto zig_block_4;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_309), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_4:;
         zig_usize const t15 = t12.f0;
         zig_T_tuple_7busize_2c_20u1_7d t16;
         t16.f1 = zig_addo_u32(&t16.f0, t10, t15, zig_as_u8(32));
         zig_u8 const t17 = t16.f1;
         zig_bool const t18 = t17 == zig_as_u8(0);
         {
          if (t18) {
           goto zig_block_5;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_310), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_5:;
         zig_usize const t19 = t16.f0;
         zig_bool const t20 = t19 < zig_as_u32(65536);
         {
          if (t20) {
           goto zig_block_6;
          } else {
           zig_breakpoint();
           zig_unreachable();
          }
         }
         zig_block_6:;
         zig_i32 const t21 = t9[t19];
         zig_bool const t22 = t21 >= zig_as_i32(0);
         {
          if (t22) {
           goto zig_block_7;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_311), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_7:;
         zig_usize const t23 = (zig_usize )t21;
         t8 = t23;
         /* var:y */
         {
          while (zig_true) {
           {
            /* file:10:11 */
            zig_usize const t24 = t8;
            zig_u32 t25;
            memcpy(&t25, &t24, sizeof(zig_u32 ));
            t25 = zig_wrap_u32(t25, zig_as_u8(32));
            zig_bool const t26 = t25 < zig_as_u32(32);
            if (t26) {
             /* file:10:38 */
             /* file:11:9 */
             zig_usize t27;
             /* file:11:25 */
             zig_usize const t28 = t4;
             zig_u32 const t29 = (zig_u32 )t28;
             zig_usize const t30 = t8;
             zig_u32 const t31 = (zig_u32 )t30;
             zig_usize const t32 = t0;
             zig_u32 const t33 = (zig_u32 )t32;
             zig_usize const t34 = generator_getIdx(t29, t31, t33);
             zig_usize * const t35 = (zig_usize * )&t27;
             (*t35) = t34;
             /* var:idx */
             /* file:12:9 */
             zig_u8 t36;
             zig_u8 * const t37 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_usize const t38 = t27;
             zig_u8 const t39 = t37[t38];
             zig_u8 * const t40 = (zig_u8 * )&t36;
             (*t40) = t39;
             /* var:blk */
             /* file:14:12 */
             {
              zig_u8 const t41 = t36;
              zig_bool const t42 = t41 == zig_as_u8(0);
              if (t42) {
               /* file:15:13 */
               zig_usize const t43 = t27;
               zig_u8 * const t44 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t45 = &(t44)[t43];
               (*t45) = zig_as_u8(8);
               goto zig_block_10;
              } else {
               goto zig_block_10;
              }
             }
             zig_block_10:;
             /* file:10:30 */
             zig_usize const t46 = t8;
             zig_T_tuple_7busize_2c_20u1_7d t47;
             t47.f1 = zig_addo_u32(&t47.f0, t46, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t48 = t47.f1;
             zig_bool const t49 = t48 == zig_as_u8(0);
             {
              if (t49) {
               goto zig_block_11;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_312), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_11:;
             zig_usize const t50 = t47.f0;
             t8 = t50;
             goto zig_block_9;
            } else {
             goto zig_block_8;
            }
           }
           zig_block_9:;
          }
         }
         zig_block_8:;
         /* file:7:23 */
         zig_usize const t51 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t52;
         t52.f1 = zig_addo_u32(&t52.f0, t51, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t53 = t52.f1;
         zig_bool const t54 = t53 == zig_as_u8(0);
         {
          if (t54) {
           goto zig_block_12;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_313), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_12:;
         zig_usize const t55 = t52.f0;
         t4 = t55;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:4:23 */
     zig_usize const t56 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t57;
     t57.f1 = zig_addo_u32(&t57.f0, t56, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t58 = t57.f1;
     zig_bool const t59 = t58 == zig_as_u8(0);
     {
      if (t59) {
       goto zig_block_13;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_water__anon_314), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_13:;
     zig_usize const t60 = t57.f0;
     t0 = t60;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_fill_lava(zig_void) {
 /* file:2:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:3:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:3:31 */
     /* file:5:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:6:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:6:31 */
         /* file:8:5 */
         zig_usize t8;
         t8 = zig_as_u32(0);
         /* var:y */
         {
          while (zig_true) {
           {
            /* file:9:11 */
            zig_usize const t9 = t8;
            zig_u32 t10;
            memcpy(&t10, &t9, sizeof(zig_u32 ));
            t10 = zig_wrap_u32(t10, zig_as_u8(32));
            zig_bool const t11 = t10 < zig_as_u32(10);
            if (t11) {
             /* file:9:30 */
             /* file:10:9 */
             zig_usize t12;
             /* file:10:25 */
             zig_usize const t13 = t4;
             zig_u32 const t14 = (zig_u32 )t13;
             zig_usize const t15 = t8;
             zig_u32 const t16 = (zig_u32 )t15;
             zig_usize const t17 = t0;
             zig_u32 const t18 = (zig_u32 )t17;
             zig_usize const t19 = generator_getIdx(t14, t16, t18);
             zig_usize * const t20 = (zig_usize * )&t12;
             (*t20) = t19;
             /* var:idx */
             /* file:11:9 */
             zig_u8 t21;
             zig_u8 * const t22 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_usize const t23 = t12;
             zig_u8 const t24 = t22[t23];
             zig_u8 * const t25 = (zig_u8 * )&t21;
             (*t25) = t24;
             /* var:blk */
             /* file:13:12 */
             {
              zig_u8 const t26 = t21;
              zig_bool const t27 = t26 == zig_as_u8(0);
              if (t27) {
               /* file:14:13 */
               zig_usize const t28 = t12;
               zig_u8 * const t29 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t30 = &(t29)[t28];
               (*t30) = zig_as_u8(8);
               goto zig_block_6;
              } else {
               goto zig_block_6;
              }
             }
             zig_block_6:;
             /* file:9:22 */
             zig_usize const t31 = t8;
             zig_T_tuple_7busize_2c_20u1_7d t32;
             t32.f1 = zig_addo_u32(&t32.f0, t31, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t33 = t32.f1;
             zig_bool const t34 = t33 == zig_as_u8(0);
             {
              if (t34) {
               goto zig_block_7;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_lava__anon_315), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_7:;
             zig_usize const t35 = t32.f0;
             t8 = t35;
             goto zig_block_5;
            } else {
             goto zig_block_4;
            }
           }
           zig_block_5:;
          }
         }
         zig_block_4:;
         /* file:6:23 */
         zig_usize const t36 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t37;
         t37.f1 = zig_addo_u32(&t37.f0, t36, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t38 = t37.f1;
         zig_bool const t39 = t38 == zig_as_u8(0);
         {
          if (t39) {
           goto zig_block_8;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_lava__anon_316), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_8:;
         zig_usize const t40 = t37.f0;
         t4 = t40;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:3:23 */
     zig_usize const t41 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t42;
     t42.f1 = zig_addo_u32(&t42.f0, t41, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t43 = t42.f1;
     zig_bool const t44 = t43 == zig_as_u8(0);
     {
      if (t44) {
       goto zig_block_9;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fill_lava__anon_317), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_9:;
     zig_usize const t45 = t42.f0;
     t0 = t45;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_create_surface(zig_void) {
 /* file:3:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:4:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(256);
    if (t3) {
     /* file:4:31 */
     /* file:6:5 */
     zig_usize t4;
     t4 = zig_as_u32(0);
     /* var:x */
     {
      while (zig_true) {
       {
        /* file:7:11 */
        zig_usize const t5 = t4;
        zig_u32 t6;
        memcpy(&t6, &t5, sizeof(zig_u32 ));
        t6 = zig_wrap_u32(t6, zig_as_u8(32));
        zig_bool const t7 = t6 < zig_as_u32(256);
        if (t7) {
         /* file:7:31 */
         /* file:9:9 */
         zig_f32 t8;
         zig_usize const t9 = t4;
         zig_f32 const t10 = __floatunsisf(t9);
         zig_f32 * const t11 = (zig_f32 * )&t8;
         (*t11) = t10;
         /* var:xf */
         /* file:10:9 */
         zig_f32 t12;
         zig_usize const t13 = t0;
         zig_f32 const t14 = __floatunsisf(t13);
         zig_f32 * const t15 = (zig_f32 * )&t12;
         (*t15) = t14;
         /* var:zf */
         /* file:12:9 */
         zig_bool t16;
         /* file:12:36 */
         zig_f32 const t17 = t8;
         zig_f32 const t18 = t12;
         zig_u32 const t19 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
         zig_T_tuple_7bu32_2c_20u1_7d t20;
         t20.f1 = zig_addo_u32(&t20.f0, t19, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t21 = t20.f1;
         zig_bool const t22 = t21 == zig_as_u8(0);
         {
          if (t22) {
           goto zig_block_4;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_318), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_4:;
         zig_u32 const t23 = t20.f0;
         zig_f64 const t24 = __extendsfdf2(t17);
         zig_f64 const t25 = __extendsfdf2(t18);
         zig_f64 const t26 = perlin_onoise(zig_as_u32(8), t24, t25, t23);
         zig_bool const t27 = zig_gt_f64(t26, (zig_f64 )zig_as_f64(0x1p3, zig_as_i64(0x4020000000000000))) > zig_as_i8(0);
         zig_bool * const t28 = (zig_bool * )&t16;
         (*t28) = t27;
         /* var:is_sand */
         /* file:13:9 */
         zig_bool t29;
         /* file:13:38 */
         zig_f32 const t30 = t8;
         zig_f32 const t31 = t12;
         zig_u32 const t32 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
         zig_T_tuple_7bu32_2c_20u1_7d t33;
         t33.f1 = zig_addo_u32(&t33.f0, t32, zig_as_u32(2), zig_as_u8(32));
         zig_u8 const t34 = t33.f1;
         zig_bool const t35 = t34 == zig_as_u8(0);
         {
          if (t35) {
           goto zig_block_5;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_319), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_5:;
         zig_u32 const t36 = t33.f0;
         zig_f64 const t37 = __extendsfdf2(t30);
         zig_f64 const t38 = __extendsfdf2(t31);
         zig_f64 const t39 = perlin_onoise(zig_as_u32(8), t37, t38, t36);
         zig_bool const t40 = zig_gt_f64(t39, (zig_f64 )zig_as_f64(0x1.8p3, zig_as_i64(0x4028000000000000))) > zig_as_i8(0);
         zig_bool * const t41 = (zig_bool * )&t29;
         (*t41) = t40;
         /* var:is_gravel */
         /* file:15:9 */
         zig_i32 t42;
         zig_i32 t43[zig_as_u32(65536)];
         memcpy(t43, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
         zig_usize const t44 = t4;
         zig_usize const t45 = t0;
         zig_T_tuple_7busize_2c_20u1_7d t46;
         t46.f1 = zig_mulo_u32(&t46.f0, t45, zig_as_u32(256), zig_as_u8(32));
         zig_u8 const t47 = t46.f1;
         zig_bool const t48 = t47 == zig_as_u8(0);
         {
          if (t48) {
           goto zig_block_6;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_320), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_6:;
         zig_usize const t49 = t46.f0;
         zig_T_tuple_7busize_2c_20u1_7d t50;
         t50.f1 = zig_addo_u32(&t50.f0, t44, t49, zig_as_u8(32));
         zig_u8 const t51 = t50.f1;
         zig_bool const t52 = t51 == zig_as_u8(0);
         {
          if (t52) {
           goto zig_block_7;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_321), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_7:;
         zig_usize const t53 = t50.f0;
         zig_bool const t54 = t53 < zig_as_u32(65536);
         {
          if (t54) {
           goto zig_block_8;
          } else {
           zig_breakpoint();
           zig_unreachable();
          }
         }
         zig_block_8:;
         zig_i32 const t55 = t43[t53];
         zig_i32 * const t56 = (zig_i32 * )&t42;
         (*t56) = t55;
         /* var:y */
         /* file:17:9 */
         zig_u8 t57;
         zig_u8 * const t58 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
         /* file:17:36 */
         zig_usize const t59 = t4;
         zig_u32 const t60 = (zig_u32 )t59;
         zig_i32 const t61 = t42;
         zig_T_tuple_7bi32_2c_20u1_7d t62;
         t62.f1 = zig_addo_i32(&t62.f0, t61, zig_as_i32(1), zig_as_u8(32));
         zig_u8 const t63 = t62.f1;
         zig_bool const t64 = t63 == zig_as_u8(0);
         {
          if (t64) {
           goto zig_block_9;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_322), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_9:;
         zig_i32 const t65 = t62.f0;
         zig_bool const t66 = t65 >= zig_as_i32(0);
         {
          if (t66) {
           goto zig_block_10;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_323), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_10:;
         zig_u32 const t67 = (zig_u32 )t65;
         zig_usize const t68 = t0;
         zig_u32 const t69 = (zig_u32 )t68;
         zig_usize const t70 = generator_getIdx(t60, t67, t69);
         zig_u8 const t71 = t58[t70];
         zig_u8 * const t72 = (zig_u8 * )&t57;
         (*t72) = t71;
         /* var:blkA */
         /* file:19:9 */
         zig_usize t73;
         /* file:19:25 */
         zig_usize const t74 = t4;
         zig_u32 const t75 = (zig_u32 )t74;
         zig_i32 const t76 = t42;
         zig_bool const t77 = t76 >= zig_as_i32(0);
         {
          if (t77) {
           goto zig_block_11;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_324), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_11:;
         zig_u32 const t78 = (zig_u32 )t76;
         zig_usize const t79 = t0;
         zig_u32 const t80 = (zig_u32 )t79;
         zig_usize const t81 = generator_getIdx(t75, t78, t80);
         zig_usize * const t82 = (zig_usize * )&t73;
         (*t82) = t81;
         /* var:idx */
         /* file:21:12 */
         {
          zig_u8 const t83 = t57;
          zig_bool const t84 = t83 == zig_as_u8(8);
          zig_bool t85;
          {
           if (t84) {
            zig_bool const t86 = t29;
            t85 = t86;
            goto zig_block_13;
           } else {
            t85 = zig_false;
            goto zig_block_13;
           }
          }
          zig_block_13:;
          if (t85) {
           /* file:22:13 */
           zig_usize const t87 = t73;
           zig_u8 * const t88 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t89 = &(t88)[t87];
           (*t89) = zig_as_u8(13);
           goto zig_block_12;
          } else {
           goto zig_block_12;
          }
         }
         zig_block_12:;
         /* file:25:12 */
         {
          zig_u8 const t90 = t57;
          zig_bool const t91 = t90 == zig_as_u8(0);
          if (t91) {
           /* file:26:16 */
           {
            zig_i32 const t92 = t42;
            zig_bool const t93 = t92 <= zig_as_i32(32);
            zig_bool t94;
            {
             if (t93) {
              zig_bool const t95 = t16;
              t94 = t95;
              goto zig_block_16;
             } else {
              t94 = zig_false;
              goto zig_block_16;
             }
            }
            zig_block_16:;
            if (t94) {
             /* file:27:17 */
             zig_usize const t96 = t73;
             zig_u8 * const t97 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t98 = &(t97)[t96];
             (*t98) = zig_as_u8(12);
             goto zig_block_15;
            } else {
             /* file:29:17 */
             zig_usize const t99 = t73;
             zig_u8 * const t100 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t101 = &(t100)[t99];
             (*t101) = zig_as_u8(2);
             goto zig_block_15;
            }
           }
           zig_block_15:;
           goto zig_block_14;
          } else {
           goto zig_block_14;
          }
         }
         zig_block_14:;
         /* file:7:23 */
         zig_usize const t102 = t4;
         zig_T_tuple_7busize_2c_20u1_7d t103;
         t103.f1 = zig_addo_u32(&t103.f0, t102, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t104 = t103.f1;
         zig_bool const t105 = t104 == zig_as_u8(0);
         {
          if (t105) {
           goto zig_block_17;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_325), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_17:;
         zig_usize const t106 = t103.f0;
         t4 = t106;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:4:23 */
     zig_usize const t107 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t108;
     t108.f1 = zig_addo_u32(&t108.f0, t107, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t109 = t108.f1;
     zig_bool const t110 = t109 == zig_as_u8(0);
     {
      if (t110) {
       goto zig_block_18;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_surface__anon_326), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_18:;
     zig_usize const t111 = t108.f0;
     t0 = t111;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_create_plants(zig_void) {
 /* file:2:5 */
 /* file:4:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:5:11 */
    zig_usize const t1 = t0;
    zig_u32 t2;
    memcpy(&t2, &t1, sizeof(zig_u32 ));
    t2 = zig_wrap_u32(t2, zig_as_u8(32));
    zig_bool const t3 = t2 < zig_as_u32(21);
    if (t3) {
     /* file:5:38 */
     /* file:6:9 */
     /* file:6:23 */
     generator_create_flowers();
     /* file:5:30 */
     zig_usize const t4 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t5;
     t5.f1 = zig_addo_u32(&t5.f0, t4, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t6 = t5.f1;
     zig_bool const t7 = t6 == zig_as_u8(0);
     {
      if (t7) {
       goto zig_block_2;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_plants__anon_327), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_2:;
     zig_usize const t8 = t5.f0;
     t0 = t8;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 /* file:9:5 */
 /* file:11:5 */
 t0 = zig_as_u32(0);
 {
  while (zig_true) {
   {
    /* file:12:11 */
    zig_usize const t9 = t0;
    zig_u32 t10;
    memcpy(&t10, &t9, sizeof(zig_u32 ));
    t10 = zig_wrap_u32(t10, zig_as_u8(32));
    zig_bool const t11 = t10 < zig_as_u32(2097);
    if (t11) {
     /* file:12:40 */
     /* file:13:9 */
     /* file:13:25 */
     generator_create_mushrooms();
     /* file:12:32 */
     zig_usize const t12 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t13;
     t13.f1 = zig_addo_u32(&t13.f0, t12, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t14 = t13.f1;
     zig_bool const t15 = t14 == zig_as_u8(0);
     {
      if (t15) {
       goto zig_block_5;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_plants__anon_328), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_5:;
     zig_usize const t16 = t13.f0;
     t0 = t16;
     goto zig_block_4;
    } else {
     goto zig_block_3;
    }
   }
   zig_block_4:;
  }
 }
 zig_block_3:;
 /* file:16:5 */
 /* file:18:5 */
 t0 = zig_as_u32(0);
 {
  while (zig_true) {
   {
    /* file:19:11 */
    zig_usize const t17 = t0;
    zig_u32 t18;
    memcpy(&t18, &t17, sizeof(zig_u32 ));
    t18 = zig_wrap_u32(t18, zig_as_u8(32));
    zig_bool const t19 = t18 < zig_as_u32(16);
    if (t19) {
     /* file:19:36 */
     /* file:20:9 */
     /* file:20:20 */
     generator_create_tree();
     /* file:19:28 */
     zig_usize const t20 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t21;
     t21.f1 = zig_addo_u32(&t21.f0, t20, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t22 = t21.f1;
     zig_bool const t23 = t22 == zig_as_u8(0);
     {
      if (t23) {
       goto zig_block_8;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_plants__anon_329), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_8:;
     zig_usize const t24 = t21.f0;
     t0 = t24;
     goto zig_block_7;
    } else {
     goto zig_block_6;
    }
   }
   zig_block_7:;
  }
 }
 zig_block_6:;
 return;
}

static zig_void rand_Xoshiro256_seed(zig_S_rand_Xoshiro256__255 * const a0, zig_u64 const a1) {
 /* file:3:5 */
 zig_S_rand_SplitMix64__330 t0;
 /* file:3:39 */
 zig_S_rand_SplitMix64__330 const t1 = rand_SplitMix64_init(a1);
 zig_S_rand_SplitMix64__330 * const t2 = (zig_S_rand_SplitMix64__330 * )&t0;
 (*t2) = t1;
 /* var:gen */
 /* file:5:5 */
 zig_S_rand_Xoshiro256__255 * t3;
 t3 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t4 = (zig_S_rand_Xoshiro256__255 * const * )&t3;
 zig_S_rand_Xoshiro256__255 * const t5 = (*t4);
 zig_A_u64_4 * const t6 = (zig_A_u64_4 * )&t5->s;
 zig_u64 * const t7 = &((*t6))[zig_as_u32(0)];
 /* file:5:25 */
 zig_u64 const t8 = rand_SplitMix64_next(&t0);
 (*t7) = t8;
 /* file:6:5 */
 zig_S_rand_Xoshiro256__255 * t9;
 t9 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t10 = (zig_S_rand_Xoshiro256__255 * const * )&t9;
 zig_S_rand_Xoshiro256__255 * const t11 = (*t10);
 zig_A_u64_4 * const t12 = (zig_A_u64_4 * )&t11->s;
 zig_u64 * const t13 = &((*t12))[zig_as_u32(1)];
 /* file:6:25 */
 zig_u64 const t14 = rand_SplitMix64_next(&t0);
 (*t13) = t14;
 /* file:7:5 */
 zig_S_rand_Xoshiro256__255 * t15;
 t15 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t16 = (zig_S_rand_Xoshiro256__255 * const * )&t15;
 zig_S_rand_Xoshiro256__255 * const t17 = (*t16);
 zig_A_u64_4 * const t18 = (zig_A_u64_4 * )&t17->s;
 zig_u64 * const t19 = &((*t18))[zig_as_u32(2)];
 /* file:7:25 */
 zig_u64 const t20 = rand_SplitMix64_next(&t0);
 (*t19) = t20;
 /* file:8:5 */
 zig_S_rand_Xoshiro256__255 * t21;
 t21 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t22 = (zig_S_rand_Xoshiro256__255 * const * )&t21;
 zig_S_rand_Xoshiro256__255 * const t23 = (*t22);
 zig_A_u64_4 * const t24 = (zig_A_u64_4 * )&t23->s;
 zig_u64 * const t25 = &((*t24))[zig_as_u32(3)];
 /* file:8:25 */
 zig_u64 const t26 = rand_SplitMix64_next(&t0);
 (*t25) = t26;
 return;
}

static zig_f64 generator_noise1(zig_f32 const a0, zig_f32 const a1) {
 /* file:2:5 */
 zig_f64 t0;
 /* file:2:27 */
 zig_u32 const t1 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
 zig_T_tuple_7bu32_2c_20u1_7d t2;
 t2.f1 = zig_addo_u32(&t2.f0, t1, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t3 = t2.f1;
 zig_bool const t4 = t3 == zig_as_u8(0);
 {
  if (t4) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_noise1__anon_333), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_u32 const t5 = t2.f0;
 zig_f64 const t6 = __extendsfdf2(a0);
 zig_f64 const t7 = __extendsfdf2(a1);
 zig_f64 const t8 = perlin_onoise(zig_as_u32(8), t6, t7, t5);
 zig_f64 * const t9 = (zig_f64 * )&t0;
 (*t9) = t8;
 /* var:n1 */
 /* file:3:5 */
 zig_f64 t10;
 /* file:3:25 */
 zig_f64 const t11 = t0;
 zig_f64 const t12 = __extendsfdf2(a0);
 zig_f64 const t13 = zig_add_f64(t12, t11);
 zig_u32 const t14 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
 zig_T_tuple_7bu32_2c_20u1_7d t15;
 t15.f1 = zig_addo_u32(&t15.f0, t14, zig_as_u32(2), zig_as_u8(32));
 zig_u8 const t16 = t15.f1;
 zig_bool const t17 = t16 == zig_as_u8(0);
 {
  if (t17) {
   goto zig_block_1;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_noise1__anon_334), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_1:;
 zig_u32 const t18 = t15.f0;
 zig_f64 const t19 = __extendsfdf2(a1);
 zig_f64 const t20 = perlin_onoise(zig_as_u32(8), t13, t19, t18);
 t10 = t20;
 /* file:3:5 */
 return t10;
}

static zig_f64 generator_noise2(zig_f32 const a0, zig_f32 const a1) {
 /* file:2:5 */
 zig_f64 t0;
 /* file:2:27 */
 zig_u32 const t1 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
 zig_T_tuple_7bu32_2c_20u1_7d t2;
 t2.f1 = zig_addo_u32(&t2.f0, t1, zig_as_u32(3), zig_as_u8(32));
 zig_u8 const t3 = t2.f1;
 zig_bool const t4 = t3 == zig_as_u8(0);
 {
  if (t4) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_noise2__anon_335), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_u32 const t5 = t2.f0;
 zig_f64 const t6 = __extendsfdf2(a0);
 zig_f64 const t7 = __extendsfdf2(a1);
 zig_f64 const t8 = perlin_onoise(zig_as_u32(8), t6, t7, t5);
 zig_f64 * const t9 = (zig_f64 * )&t0;
 (*t9) = t8;
 /* var:n1 */
 /* file:3:5 */
 zig_f64 t10;
 /* file:3:25 */
 zig_f64 const t11 = t0;
 zig_f64 const t12 = __extendsfdf2(a0);
 zig_f64 const t13 = zig_add_f64(t12, t11);
 zig_u32 const t14 = (*(zig_u32 * )((zig_u32 * )&generator_map_seed));
 zig_T_tuple_7bu32_2c_20u1_7d t15;
 t15.f1 = zig_addo_u32(&t15.f0, t14, zig_as_u32(4), zig_as_u8(32));
 zig_u8 const t16 = t15.f1;
 zig_bool const t17 = t16 == zig_as_u8(0);
 {
  if (t17) {
   goto zig_block_1;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_noise2__anon_336), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_1:;
 zig_u32 const t18 = t15.f0;
 zig_f64 const t19 = __extendsfdf2(a1);
 zig_f64 const t20 = perlin_onoise(zig_as_u32(8), t13, t19, t18);
 t10 = t20;
 /* file:3:5 */
 return t10;
}

static zig_f64 perlin_onoise(zig_usize const a0, zig_f64 const a1, zig_f64 const a2, zig_u32 const a3) {
 /* file:2:5 */
 zig_f64 t0;
 t0 = (zig_f64 )zig_as_f64(0x0.0p0, zig_as_i64(0x0));
 /* var:sum */
 /* file:3:5 */
 zig_f64 t1;
 t1 = (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000));
 /* var:amp */
 /* file:4:5 */
 zig_f64 t2;
 t2 = (zig_f64 )zig_as_f64(0x1.4cccccccccccdp0, zig_as_i64(0x3ff4cccccccccccd));
 /* var:freq */
 /* file:6:5 */
 zig_usize t3;
 t3 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:7:11 */
    zig_usize const t4 = t3;
    zig_u32 t5;
    memcpy(&t5, &t4, sizeof(zig_u32 ));
    t5 = zig_wrap_u32(t5, zig_as_u8(32));
    zig_u32 t6;
    memcpy(&t6, &a0, sizeof(zig_u32 ));
    t6 = zig_wrap_u32(t6, zig_as_u8(32));
    zig_bool const t7 = t5 < t6;
    if (t7) {
     /* file:7:35 */
     /* file:8:9 */
     zig_f64 const t8 = t0;
     /* file:8:22 */
     zig_f64 const t9 = t2;
     zig_f64 const t10 = zig_mul_f64(a1, t9);
     zig_f64 const t11 = t2;
     zig_f64 const t12 = zig_mul_f64(a2, t11);
     zig_f64 const t13 = perlin_pnoise(t10, t12, a3);
     zig_f64 const t14 = t1;
     zig_f64 const t15 = zig_mul_f64(t13, t14);
     zig_f64 const t16 = zig_add_f64(t8, t15);
     t0 = t16;
     /* file:10:9 */
     zig_f64 const t17 = t1;
     zig_f64 const t18 = zig_mul_f64(t17, (zig_f64 )zig_as_f64(0x1p1, zig_as_i64(0x4000000000000000)));
     t1 = t18;
     /* file:11:9 */
     zig_f64 const t19 = t2;
     zig_f64 const t20 = zig_div_f64(t19, (zig_f64 )zig_as_f64(0x1p1, zig_as_i64(0x4000000000000000)));
     t2 = t20;
     /* file:7:27 */
     zig_usize const t21 = t3;
     zig_T_tuple_7busize_2c_20u1_7d t22;
     t22.f1 = zig_addo_u32(&t22.f0, t21, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t23 = t22.f1;
     zig_bool const t24 = t23 == zig_as_u8(0);
     {
      if (t24) {
       goto zig_block_2;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_onoise__anon_337), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_2:;
     zig_usize const t25 = t22.f0;
     t3 = t25;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 /* file:13:5 */
 zig_f64 const t26 = t0;
 /* file:13:5 */
 return t26;
}

static zig_cold zig_noreturn builtin_default_panic(zig_L_u8 const a0, zig_S_builtin_StackTrace__277 * const a1, zig_Q_usize const a2) {
 /* file:2:5 */
 /* file:6:9 */
 while (zig_true) {
  /* file:15:16 */
  /* file:15:22 */
  /* file:16:13 */
  zig_breakpoint();
 }
}
static zig_i32 generator_waterLevel = zig_as_i32(32);

static zig_usize generator_getIdx(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2) {
 /* file:2:8 */
 {
  zig_bool const t0 = a0 < zig_as_u32(256);
  zig_bool t1;
  {
   if (t0) {
    t1 = zig_true;
    goto zig_block_1;
   } else {
    t1 = zig_false;
    goto zig_block_1;
   }
  }
  zig_block_1:;
  zig_bool t2;
  {
   if (t1) {
    zig_bool const t3 = a1 < zig_as_u32(64);
    t2 = t3;
    goto zig_block_2;
   } else {
    t2 = zig_false;
    goto zig_block_2;
   }
  }
  zig_block_2:;
  zig_bool t4;
  {
   if (t2) {
    t4 = zig_true;
    goto zig_block_3;
   } else {
    t4 = zig_false;
    goto zig_block_3;
   }
  }
  zig_block_3:;
  zig_bool t5;
  {
   if (t4) {
    zig_bool const t6 = a2 < zig_as_u32(256);
    t5 = t6;
    goto zig_block_4;
   } else {
    t5 = zig_false;
    goto zig_block_4;
   }
  }
  zig_block_4:;
  if (t5) {
   /* file:3:9 */
   zig_T_tuple_7bu32_2c_20u1_7d t7;
   t7.f1 = zig_mulo_u32(&t7.f0, a1, zig_as_u32(256), zig_as_u8(32));
   zig_u8 const t8 = t7.f1;
   zig_bool const t9 = t8 == zig_as_u8(0);
   {
    if (t9) {
     goto zig_block_5;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_getIdx__anon_338), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_5:;
   zig_u32 const t10 = t7.f0;
   zig_T_tuple_7bu32_2c_20u1_7d t11;
   t11.f1 = zig_mulo_u32(&t11.f0, t10, zig_as_u32(256), zig_as_u8(32));
   zig_u8 const t12 = t11.f1;
   zig_bool const t13 = t12 == zig_as_u8(0);
   {
    if (t13) {
     goto zig_block_6;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_getIdx__anon_339), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_6:;
   zig_u32 const t14 = t11.f0;
   zig_T_tuple_7bu32_2c_20u1_7d t15;
   t15.f1 = zig_mulo_u32(&t15.f0, a2, zig_as_u32(256), zig_as_u8(32));
   zig_u8 const t16 = t15.f1;
   zig_bool const t17 = t16 == zig_as_u8(0);
   {
    if (t17) {
     goto zig_block_7;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_getIdx__anon_340), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_7:;
   zig_u32 const t18 = t15.f0;
   zig_T_tuple_7bu32_2c_20u1_7d t19;
   t19.f1 = zig_addo_u32(&t19.f0, t14, t18, zig_as_u8(32));
   zig_u8 const t20 = t19.f1;
   zig_bool const t21 = t20 == zig_as_u8(0);
   {
    if (t21) {
     goto zig_block_8;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_getIdx__anon_341), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_8:;
   zig_u32 const t22 = t19.f0;
   zig_T_tuple_7bu32_2c_20u1_7d t23;
   t23.f1 = zig_addo_u32(&t23.f0, t22, a0, zig_as_u8(32));
   zig_u8 const t24 = t23.f1;
   zig_bool const t25 = t24 == zig_as_u8(0);
   {
    if (t25) {
     goto zig_block_9;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_getIdx__anon_342), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_9:;
   zig_u32 const t26 = t23.f0;
   zig_usize t27;
   memcpy(&t27, &t26, sizeof(zig_usize ));
   t27 = zig_wrap_u32(t27, zig_as_u8(32));
   /* file:3:9 */
   return t27;
  } else {
   goto zig_block_0;
  }
 }
 zig_block_0:;
 /* file:5:5 */
 /* file:5:5 */
 return zig_as_u32(0);
}

static zig_void generator_create_cave(zig_void) {
 /* file:2:5 */
 zig_f32 t0;
 /* file:2:41 */
 zig_S_rand_Random__343 const t1 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t2;
 t2 = t1;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:2:47 */
 zig_u32 const t5 = rand_Random_int__anon_448(t4);
 zig_u32 const t6 = t5 % zig_as_u32(256);
 zig_f32 const t7 = __floatunsisf(t6);
 zig_f32 * const t8 = (zig_f32 * )&t0;
 (*t8) = t7;
 /* var:vx */
 /* file:3:5 */
 zig_f32 t9;
 /* file:3:41 */
 zig_S_rand_Random__343 const t10 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t11;
 t11 = t10;
 zig_S_rand_Random__343 const * const t12 = (zig_S_rand_Random__343 const * )&t11;
 zig_S_rand_Random__343 const t13 = (*t12);
 /* file:3:47 */
 zig_u32 const t14 = rand_Random_int__anon_448(t13);
 zig_u32 const t15 = t14 % zig_as_u32(64);
 zig_f32 const t16 = __floatunsisf(t15);
 zig_f32 * const t17 = (zig_f32 * )&t9;
 (*t17) = t16;
 /* var:vy */
 /* file:4:5 */
 zig_f32 t18;
 /* file:4:41 */
 zig_S_rand_Random__343 const t19 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t20;
 t20 = t19;
 zig_S_rand_Random__343 const * const t21 = (zig_S_rand_Random__343 const * )&t20;
 zig_S_rand_Random__343 const t22 = (*t21);
 /* file:4:47 */
 zig_u32 const t23 = rand_Random_int__anon_448(t22);
 zig_u32 const t24 = t23 % zig_as_u32(256);
 zig_f32 const t25 = __floatunsisf(t24);
 zig_f32 * const t26 = (zig_f32 * )&t18;
 (*t26) = t25;
 /* var:vz */
 /* file:6:5 */
 zig_f32 t27;
 /* file:6:28 */
 /* file:6:39 */
 zig_S_rand_Random__343 const t28 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t29;
 t29 = t28;
 zig_S_rand_Random__343 const * const t30 = (zig_S_rand_Random__343 const * )&t29;
 zig_S_rand_Random__343 const t31 = (*t30);
 /* file:6:47 */
 zig_f32 const t32 = rand_Random_float__anon_695(t31);
 /* file:6:65 */
 zig_S_rand_Random__343 const t33 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t34;
 t34 = t33;
 zig_S_rand_Random__343 const * const t35 = (zig_S_rand_Random__343 const * )&t34;
 zig_S_rand_Random__343 const t36 = (*t35);
 /* file:6:73 */
 zig_f32 const t37 = rand_Random_float__anon_695(t36);
 zig_f32 const t38 = zig_add_f32(t32, t37);
 /* dbg func:floor */
 /* var:value */
 /* file:2:5 */
 zig_f32 const t39 = zig_libc_name_f32(floor)(t38);
 /* file:2:5 */
 /* dbg func:create_cave */
 zig_f32 const t40 = zig_mul_f32(t39, (zig_f32 )zig_as_f32(0x1.9p7, zig_as_i32(0x43480000)));
 zig_f32 * const t41 = (zig_f32 * )&t27;
 (*t41) = t40;
 /* var:vl */
 /* file:8:5 */
 zig_f32 t42;
 /* file:8:27 */
 zig_S_rand_Random__343 const t43 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t44;
 t44 = t43;
 zig_S_rand_Random__343 const * const t45 = (zig_S_rand_Random__343 const * )&t44;
 zig_S_rand_Random__343 const t46 = (*t45);
 /* file:8:35 */
 zig_f32 const t47 = rand_Random_float__anon_695(t46);
 zig_f32 const t48 = zig_mul_f32(t47, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
 zig_f32 const t49 = zig_mul_f32(t48, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
 zig_f32 * const t50 = (zig_f32 * )&t42;
 (*t50) = t49;
 /* var:theta */
 /* file:9:5 */
 zig_f32 t51;
 t51 = (zig_f32 )zig_as_f32(0x0.0p0, zig_as_i32(0x0));
 /* var:deltaTheta */
 /* file:11:5 */
 zig_f32 t52;
 /* file:11:25 */
 zig_S_rand_Random__343 const t53 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t54;
 t54 = t53;
 zig_S_rand_Random__343 const * const t55 = (zig_S_rand_Random__343 const * )&t54;
 zig_S_rand_Random__343 const t56 = (*t55);
 /* file:11:33 */
 zig_f32 const t57 = rand_Random_float__anon_695(t56);
 zig_f32 const t58 = zig_mul_f32(t57, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
 zig_f32 const t59 = zig_mul_f32(t58, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
 zig_f32 * const t60 = (zig_f32 * )&t52;
 (*t60) = t59;
 /* var:phi */
 /* file:12:5 */
 zig_f32 t61;
 t61 = (zig_f32 )zig_as_f32(0x0.0p0, zig_as_i32(0x0));
 /* var:deltaPhi */
 /* file:14:5 */
 zig_f32 t62;
 /* file:14:32 */
 zig_S_rand_Random__343 const t63 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t64;
 t64 = t63;
 zig_S_rand_Random__343 const * const t65 = (zig_S_rand_Random__343 const * )&t64;
 zig_S_rand_Random__343 const t66 = (*t65);
 /* file:14:40 */
 zig_f32 const t67 = rand_Random_float__anon_695(t66);
 /* file:14:58 */
 zig_S_rand_Random__343 const t68 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t69;
 t69 = t68;
 zig_S_rand_Random__343 const * const t70 = (zig_S_rand_Random__343 const * )&t69;
 zig_S_rand_Random__343 const t71 = (*t70);
 /* file:14:66 */
 zig_f32 const t72 = rand_Random_float__anon_695(t71);
 zig_f32 const t73 = zig_mul_f32(t67, t72);
 zig_f32 const t74 = zig_mul_f32(t73, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
 zig_f32 * const t75 = (zig_f32 * )&t62;
 (*t75) = t74;
 /* var:caveRadius */
 /* file:16:5 */
 zig_usize t76;
 t76 = zig_as_u32(0);
 /* var:len */
 {
  while (zig_true) {
   {
    /* file:17:11 */
    zig_usize const t77 = t76;
    zig_f32 const t78 = t27;
    zig_usize const t79 = zig_wrap_u32(__fixunssfsi(t78), zig_as_u8(32));
    zig_f32 const t80 = __floatunsisf(t79);
    zig_f32 const t81 = zig_sub_f32(t78, t80);
    zig_bool const t82 = zig_lt_f32(t81, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
    zig_bool const t83 = zig_gt_f32(t81, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
    zig_bool const t84 = t82 & t83;
    {
     if (t84) {
      goto zig_block_2;
     } else {
      builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_696), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
     }
    }
    zig_block_2:;
    zig_u32 t85;
    memcpy(&t85, &t77, sizeof(zig_u32 ));
    t85 = zig_wrap_u32(t85, zig_as_u8(32));
    zig_u32 t86;
    memcpy(&t86, &t79, sizeof(zig_u32 ));
    t86 = zig_wrap_u32(t86, zig_as_u8(32));
    zig_bool const t87 = t85 < t86;
    if (t87) {
     /* file:17:54 */
     /* file:18:9 */
     zig_f32 const t88 = t0;
     /* file:18:27 */
     zig_f32 const t89 = t42;
     /* dbg func:sin */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t90 = zig_libc_name_f32(sin)(t89);
     /* file:2:5 */
     /* dbg func:create_cave */
     /* file:18:49 */
     zig_f32 const t91 = t52;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t92 = zig_libc_name_f32(cos)(t91);
     /* file:2:5 */
     /* dbg func:create_cave */
     zig_f32 const t93 = zig_mul_f32(t90, t92);
     zig_f32 const t94 = zig_add_f32(t88, t93);
     t0 = t94;
     /* file:19:9 */
     zig_f32 const t95 = t9;
     /* file:19:27 */
     zig_f32 const t96 = t42;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t97 = zig_libc_name_f32(cos)(t96);
     /* file:2:5 */
     /* dbg func:create_cave */
     /* file:19:49 */
     zig_f32 const t98 = t52;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t99 = zig_libc_name_f32(cos)(t98);
     /* file:2:5 */
     /* dbg func:create_cave */
     zig_f32 const t100 = zig_mul_f32(t97, t99);
     zig_f32 const t101 = zig_add_f32(t95, t100);
     t9 = t101;
     /* file:20:9 */
     zig_f32 const t102 = t18;
     /* file:20:27 */
     zig_f32 const t103 = t52;
     /* dbg func:sin */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t104 = zig_libc_name_f32(sin)(t103);
     /* file:2:5 */
     /* dbg func:create_cave */
     zig_f32 const t105 = zig_add_f32(t102, t104);
     t18 = t105;
     /* file:22:9 */
     zig_f32 const t106 = t42;
     zig_f32 const t107 = t51;
     zig_f32 const t108 = zig_mul_f32(t107, (zig_f32 )zig_as_f32(0x1.99999ap-3, zig_as_i32(0x3e4ccccd)));
     zig_f32 const t109 = zig_add_f32(t106, t108);
     t42 = t109;
     /* file:23:9 */
     zig_f32 const t110 = t51;
     zig_f32 const t111 = zig_mul_f32(t110, (zig_f32 )zig_as_f32(0x1.ccccccp-1, zig_as_i32(0x3f666666)));
     t51 = t111;
     /* file:24:9 */
     zig_f32 const t112 = t51;
     /* file:24:33 */
     zig_S_rand_Random__343 const t113 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t114;
     t114 = t113;
     zig_S_rand_Random__343 const * const t115 = (zig_S_rand_Random__343 const * )&t114;
     zig_S_rand_Random__343 const t116 = (*t115);
     /* file:24:41 */
     zig_f32 const t117 = rand_Random_float__anon_695(t116);
     /* file:24:59 */
     zig_S_rand_Random__343 const t118 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t119;
     t119 = t118;
     zig_S_rand_Random__343 const * const t120 = (zig_S_rand_Random__343 const * )&t119;
     zig_S_rand_Random__343 const t121 = (*t120);
     /* file:24:67 */
     zig_f32 const t122 = rand_Random_float__anon_695(t121);
     zig_f32 const t123 = zig_sub_f32(t117, t122);
     zig_f32 const t124 = zig_add_f32(t112, t123);
     t51 = t124;
     /* file:26:9 */
     zig_f32 const t125 = t52;
     zig_f32 const t126 = zig_div_f32(t125, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
     t52 = t126;
     /* file:27:9 */
     zig_f32 const t127 = t52;
     zig_f32 const t128 = t61;
     zig_f32 const t129 = zig_div_f32(t128, (zig_f32 )zig_as_f32(0x1p2, zig_as_i32(0x40800000)));
     zig_f32 const t130 = zig_add_f32(t127, t129);
     t52 = t130;
     /* file:29:9 */
     zig_f32 const t131 = t61;
     zig_f32 const t132 = zig_mul_f32(t131, (zig_f32 )zig_as_f32(0x1.8p-1, zig_as_i32(0x3f400000)));
     t61 = t132;
     /* file:30:9 */
     zig_f32 const t133 = t61;
     /* file:30:31 */
     zig_S_rand_Random__343 const t134 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t135;
     t135 = t134;
     zig_S_rand_Random__343 const * const t136 = (zig_S_rand_Random__343 const * )&t135;
     zig_S_rand_Random__343 const t137 = (*t136);
     /* file:30:39 */
     zig_f32 const t138 = rand_Random_float__anon_695(t137);
     /* file:30:57 */
     zig_S_rand_Random__343 const t139 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t140;
     t140 = t139;
     zig_S_rand_Random__343 const * const t141 = (zig_S_rand_Random__343 const * )&t140;
     zig_S_rand_Random__343 const t142 = (*t141);
     /* file:30:65 */
     zig_f32 const t143 = rand_Random_float__anon_695(t142);
     zig_f32 const t144 = zig_sub_f32(t138, t143);
     zig_f32 const t145 = zig_add_f32(t133, t144);
     t61 = t145;
     /* file:32:12 */
     {
      /* file:32:22 */
      zig_S_rand_Random__343 const t146 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
      zig_S_rand_Random__343 t147;
      t147 = t146;
      zig_S_rand_Random__343 const * const t148 = (zig_S_rand_Random__343 const * )&t147;
      zig_S_rand_Random__343 const t149 = (*t148);
      /* file:32:30 */
      zig_f32 const t150 = rand_Random_float__anon_695(t149);
      zig_bool const t151 = zig_ge_f32(t150, (zig_f32 )zig_as_f32(0x1p-2, zig_as_i32(0x3e800000))) >= zig_as_i8(0);
      if (t151) {
       /* file:33:13 */
       zig_f32 t152;
       zig_f32 const t153 = t0;
       /* file:33:59 */
       zig_S_rand_Random__343 const t154 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
       zig_S_rand_Random__343 t155;
       t155 = t154;
       zig_S_rand_Random__343 const * const t156 = (zig_S_rand_Random__343 const * )&t155;
       zig_S_rand_Random__343 const t157 = (*t156);
       /* file:33:65 */
       zig_i32 const t158 = rand_Random_int__anon_697(t157);
       zig_i32 const t159 = zig_mod_i32(t158, zig_as_i32(4));
       zig_T_tuple_7bi32_2c_20u1_7d t160;
       t160.f1 = zig_subo_i32(&t160.f0, t159, zig_as_i32(2), zig_as_u8(32));
       zig_u8 const t161 = t160.f1;
       zig_bool const t162 = t161 == zig_as_u8(0);
       {
        if (t162) {
         goto zig_block_4;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_698), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_4:;
       zig_i32 const t163 = t160.f0;
       zig_f32 const t164 = __floatsisf(t163);
       zig_f32 const t165 = zig_mul_f32(t164, (zig_f32 )zig_as_f32(0x1.99999ap-3, zig_as_i32(0x3e4ccccd)));
       zig_f32 const t166 = zig_add_f32(t153, t165);
       zig_f32 * const t167 = (zig_f32 * )&t152;
       (*t167) = t166;
       /* var:cx */
       /* file:34:13 */
       zig_f32 t168;
       zig_f32 const t169 = t9;
       /* file:34:59 */
       zig_S_rand_Random__343 const t170 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
       zig_S_rand_Random__343 t171;
       t171 = t170;
       zig_S_rand_Random__343 const * const t172 = (zig_S_rand_Random__343 const * )&t171;
       zig_S_rand_Random__343 const t173 = (*t172);
       /* file:34:65 */
       zig_i32 const t174 = rand_Random_int__anon_697(t173);
       zig_i32 const t175 = zig_mod_i32(t174, zig_as_i32(4));
       zig_T_tuple_7bi32_2c_20u1_7d t176;
       t176.f1 = zig_subo_i32(&t176.f0, t175, zig_as_i32(2), zig_as_u8(32));
       zig_u8 const t177 = t176.f1;
       zig_bool const t178 = t177 == zig_as_u8(0);
       {
        if (t178) {
         goto zig_block_5;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_699), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_5:;
       zig_i32 const t179 = t176.f0;
       zig_f32 const t180 = __floatsisf(t179);
       zig_f32 const t181 = zig_mul_f32(t180, (zig_f32 )zig_as_f32(0x1.99999ap-3, zig_as_i32(0x3e4ccccd)));
       zig_f32 const t182 = zig_add_f32(t169, t181);
       zig_f32 * const t183 = (zig_f32 * )&t168;
       (*t183) = t182;
       /* var:cy */
       /* file:35:13 */
       zig_f32 t184;
       zig_f32 const t185 = t18;
       /* file:35:59 */
       zig_S_rand_Random__343 const t186 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
       zig_S_rand_Random__343 t187;
       t187 = t186;
       zig_S_rand_Random__343 const * const t188 = (zig_S_rand_Random__343 const * )&t187;
       zig_S_rand_Random__343 const t189 = (*t188);
       /* file:35:65 */
       zig_i32 const t190 = rand_Random_int__anon_697(t189);
       zig_i32 const t191 = zig_mod_i32(t190, zig_as_i32(4));
       zig_T_tuple_7bi32_2c_20u1_7d t192;
       t192.f1 = zig_subo_i32(&t192.f0, t191, zig_as_i32(2), zig_as_u8(32));
       zig_u8 const t193 = t192.f1;
       zig_bool const t194 = t193 == zig_as_u8(0);
       {
        if (t194) {
         goto zig_block_6;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_700), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_6:;
       zig_i32 const t195 = t192.f0;
       zig_f32 const t196 = __floatsisf(t195);
       zig_f32 const t197 = zig_mul_f32(t196, (zig_f32 )zig_as_f32(0x1.99999ap-3, zig_as_i32(0x3e4ccccd)));
       zig_f32 const t198 = zig_add_f32(t185, t197);
       zig_f32 * const t199 = (zig_f32 * )&t184;
       (*t199) = t198;
       /* var:cz */
       /* file:37:13 */
       zig_f32 t200;
       zig_f32 const t201 = t168;
       zig_f32 const t202 = zig_sub_f32((zig_f32 )zig_as_f32(0x1p6, zig_as_i32(0x42800000)), t201);
       zig_f32 const t203 = zig_div_f32(t202, (zig_f32 )zig_as_f32(0x1p6, zig_as_i32(0x42800000)));
       zig_f32 * const t204 = (zig_f32 * )&t200;
       (*t204) = t203;
       /* var:radius */
       /* file:38:13 */
       zig_f32 const t205 = t200;
       zig_f32 const t206 = zig_mul_f32(t205, (zig_f32 )zig_as_f32(0x1.cp1, zig_as_i32(0x40600000)));
       zig_f32 const t207 = zig_add_f32(t206, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000)));
       zig_f32 const t208 = t62;
       zig_f32 const t209 = zig_mul_f32(t207, t208);
       zig_f32 const t210 = zig_add_f32((zig_f32 )zig_as_f32(0x1.333334p0, zig_as_i32(0x3f99999a)), t209);
       t200 = t210;
       /* file:39:13 */
       zig_f32 const t211 = t200;
       /* file:39:43 */
       zig_usize const t212 = t76;
       zig_f32 const t213 = __floatunsisf(t212);
       zig_f32 const t214 = zig_mul_f32(t213, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
       zig_f32 const t215 = t27;
       zig_f32 const t216 = zig_div_f32(t214, t215);
       /* dbg func:sin */
       /* var:value */
       /* file:2:5 */
       zig_f32 const t217 = zig_libc_name_f32(sin)(t216);
       /* file:2:5 */
       /* dbg func:create_cave */
       zig_f32 const t218 = zig_mul_f32(t211, t217);
       t200 = t218;
       /* file:41:13 */
       /* file:41:31 */
       zig_f32 const t219 = t152;
       zig_i32 const t220 = zig_wrap_i32(__fixsfsi(t219), zig_as_u8(32));
       zig_f32 const t221 = __floatsisf(t220);
       zig_f32 const t222 = zig_sub_f32(t219, t221);
       zig_bool const t223 = zig_lt_f32(t222, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
       zig_bool const t224 = zig_gt_f32(t222, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
       zig_bool const t225 = t223 & t224;
       {
        if (t225) {
         goto zig_block_7;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_701), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_7:;
       zig_f32 const t226 = t168;
       zig_i32 const t227 = zig_wrap_i32(__fixsfsi(t226), zig_as_u8(32));
       zig_f32 const t228 = __floatsisf(t227);
       zig_f32 const t229 = zig_sub_f32(t226, t228);
       zig_bool const t230 = zig_lt_f32(t229, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
       zig_bool const t231 = zig_gt_f32(t229, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
       zig_bool const t232 = t230 & t231;
       {
        if (t232) {
         goto zig_block_8;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_702), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_8:;
       zig_f32 const t233 = t184;
       zig_i32 const t234 = zig_wrap_i32(__fixsfsi(t233), zig_as_u8(32));
       zig_f32 const t235 = __floatsisf(t234);
       zig_f32 const t236 = zig_sub_f32(t233, t235);
       zig_bool const t237 = zig_lt_f32(t236, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
       zig_bool const t238 = zig_gt_f32(t236, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
       zig_bool const t239 = t237 & t238;
       {
        if (t239) {
         goto zig_block_9;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_703), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_9:;
       zig_f32 const t240 = t200;
       generator_fillOblateSpheroid(t220, t227, t234, t240, zig_as_u8(0));
       goto zig_block_3;
      } else {
       goto zig_block_3;
      }
     }
     zig_block_3:;
     /* file:17:44 */
     zig_usize const t241 = t76;
     zig_T_tuple_7busize_2c_20u1_7d t242;
     t242.f1 = zig_addo_u32(&t242.f0, t241, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t243 = t242.f1;
     zig_bool const t244 = t243 == zig_as_u8(0);
     {
      if (t244) {
       goto zig_block_10;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_cave__anon_704), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_10:;
     zig_usize const t245 = t242.f0;
     t76 = t245;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_create_vein(zig_f32 const a0, zig_u8 const a1) {
 /* file:2:5 */
 zig_f32 t0;
 /* file:2:41 */
 zig_S_rand_Random__343 const t1 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t2;
 t2 = t1;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:2:47 */
 zig_u32 const t5 = rand_Random_int__anon_448(t4);
 zig_u32 const t6 = t5 % zig_as_u32(256);
 zig_f32 const t7 = __floatunsisf(t6);
 zig_f32 * const t8 = (zig_f32 * )&t0;
 (*t8) = t7;
 /* var:vx */
 /* file:3:5 */
 zig_f32 t9;
 /* file:3:41 */
 zig_S_rand_Random__343 const t10 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t11;
 t11 = t10;
 zig_S_rand_Random__343 const * const t12 = (zig_S_rand_Random__343 const * )&t11;
 zig_S_rand_Random__343 const t13 = (*t12);
 /* file:3:47 */
 zig_u32 const t14 = rand_Random_int__anon_448(t13);
 zig_u32 const t15 = t14 % zig_as_u32(64);
 zig_f32 const t16 = __floatunsisf(t15);
 zig_f32 * const t17 = (zig_f32 * )&t9;
 (*t17) = t16;
 /* var:vy */
 /* file:4:5 */
 zig_f32 t18;
 /* file:4:41 */
 zig_S_rand_Random__343 const t19 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t20;
 t20 = t19;
 zig_S_rand_Random__343 const * const t21 = (zig_S_rand_Random__343 const * )&t20;
 zig_S_rand_Random__343 const t22 = (*t21);
 /* file:4:47 */
 zig_u32 const t23 = rand_Random_int__anon_448(t22);
 zig_u32 const t24 = t23 % zig_as_u32(256);
 zig_f32 const t25 = __floatunsisf(t24);
 zig_f32 * const t26 = (zig_f32 * )&t18;
 (*t26) = t25;
 /* var:vz */
 /* file:6:5 */
 zig_f32 t27;
 /* file:6:24 */
 zig_S_rand_Random__343 const t28 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t29;
 t29 = t28;
 zig_S_rand_Random__343 const * const t30 = (zig_S_rand_Random__343 const * )&t29;
 zig_S_rand_Random__343 const t31 = (*t30);
 /* file:6:32 */
 zig_f32 const t32 = rand_Random_float__anon_695(t31);
 /* file:6:50 */
 zig_S_rand_Random__343 const t33 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t34;
 t34 = t33;
 zig_S_rand_Random__343 const * const t35 = (zig_S_rand_Random__343 const * )&t34;
 zig_S_rand_Random__343 const t36 = (*t35);
 /* file:6:58 */
 zig_f32 const t37 = rand_Random_float__anon_695(t36);
 zig_f32 const t38 = zig_mul_f32(t32, t37);
 zig_f32 const t39 = zig_mul_f32(t38, (zig_f32 )zig_as_f32(0x1.2cp7, zig_as_i32(0x43160000)));
 zig_f32 const t40 = zig_mul_f32(t39, a0);
 zig_f32 * const t41 = (zig_f32 * )&t27;
 (*t41) = t40;
 /* var:vl */
 /* file:8:5 */
 zig_f32 t42;
 /* file:8:27 */
 zig_S_rand_Random__343 const t43 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t44;
 t44 = t43;
 zig_S_rand_Random__343 const * const t45 = (zig_S_rand_Random__343 const * )&t44;
 zig_S_rand_Random__343 const t46 = (*t45);
 /* file:8:35 */
 zig_f32 const t47 = rand_Random_float__anon_695(t46);
 zig_f32 const t48 = zig_mul_f32(t47, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
 zig_f32 const t49 = zig_mul_f32(t48, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
 zig_f32 * const t50 = (zig_f32 * )&t42;
 (*t50) = t49;
 /* var:theta */
 /* file:9:5 */
 zig_f32 t51;
 t51 = (zig_f32 )zig_as_f32(0x0.0p0, zig_as_i32(0x0));
 /* var:deltaTheta */
 /* file:11:5 */
 zig_f32 t52;
 /* file:11:25 */
 zig_S_rand_Random__343 const t53 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t54;
 t54 = t53;
 zig_S_rand_Random__343 const * const t55 = (zig_S_rand_Random__343 const * )&t54;
 zig_S_rand_Random__343 const t56 = (*t55);
 /* file:11:33 */
 zig_f32 const t57 = rand_Random_float__anon_695(t56);
 zig_f32 const t58 = zig_mul_f32(t57, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
 zig_f32 const t59 = zig_mul_f32(t58, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
 zig_f32 * const t60 = (zig_f32 * )&t52;
 (*t60) = t59;
 /* var:phi */
 /* file:12:5 */
 zig_f32 t61;
 t61 = (zig_f32 )zig_as_f32(0x0.0p0, zig_as_i32(0x0));
 /* var:deltaPhi */
 /* file:14:5 */
 zig_usize t62;
 t62 = zig_as_u32(0);
 /* var:len */
 {
  while (zig_true) {
   {
    /* file:15:11 */
    zig_usize const t63 = t62;
    zig_f32 const t64 = t27;
    zig_usize const t65 = zig_wrap_u32(__fixunssfsi(t64), zig_as_u8(32));
    zig_f32 const t66 = __floatunsisf(t65);
    zig_f32 const t67 = zig_sub_f32(t64, t66);
    zig_bool const t68 = zig_lt_f32(t67, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
    zig_bool const t69 = zig_gt_f32(t67, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
    zig_bool const t70 = t68 & t69;
    {
     if (t70) {
      goto zig_block_2;
     } else {
      builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_vein__anon_705), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
     }
    }
    zig_block_2:;
    zig_u32 t71;
    memcpy(&t71, &t63, sizeof(zig_u32 ));
    t71 = zig_wrap_u32(t71, zig_as_u8(32));
    zig_u32 t72;
    memcpy(&t72, &t65, sizeof(zig_u32 ));
    t72 = zig_wrap_u32(t72, zig_as_u8(32));
    zig_bool const t73 = t71 < t72;
    if (t73) {
     /* file:15:54 */
     /* file:16:9 */
     zig_f32 const t74 = t0;
     /* file:16:27 */
     zig_f32 const t75 = t42;
     /* dbg func:sin */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t76 = zig_libc_name_f32(sin)(t75);
     /* file:2:5 */
     /* dbg func:create_vein */
     /* file:16:49 */
     zig_f32 const t77 = t52;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t78 = zig_libc_name_f32(cos)(t77);
     /* file:2:5 */
     /* dbg func:create_vein */
     zig_f32 const t79 = zig_mul_f32(t76, t78);
     zig_f32 const t80 = zig_add_f32(t74, t79);
     t0 = t80;
     /* file:17:9 */
     zig_f32 const t81 = t9;
     /* file:17:27 */
     zig_f32 const t82 = t42;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t83 = zig_libc_name_f32(cos)(t82);
     /* file:2:5 */
     /* dbg func:create_vein */
     /* file:17:49 */
     zig_f32 const t84 = t52;
     /* dbg func:cos */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t85 = zig_libc_name_f32(cos)(t84);
     /* file:2:5 */
     /* dbg func:create_vein */
     zig_f32 const t86 = zig_mul_f32(t83, t85);
     zig_f32 const t87 = zig_add_f32(t81, t86);
     t9 = t87;
     /* file:18:9 */
     zig_f32 const t88 = t18;
     /* file:18:27 */
     zig_f32 const t89 = t52;
     /* dbg func:sin */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t90 = zig_libc_name_f32(sin)(t89);
     /* file:2:5 */
     /* dbg func:create_vein */
     zig_f32 const t91 = zig_add_f32(t88, t90);
     t18 = t91;
     /* file:20:9 */
     zig_f32 const t92 = t51;
     zig_f32 const t93 = zig_mul_f32(t92, (zig_f32 )zig_as_f32(0x1.99999ap-3, zig_as_i32(0x3e4ccccd)));
     t42 = t93;
     /* file:21:9 */
     zig_f32 const t94 = t51;
     zig_f32 const t95 = zig_mul_f32(t94, (zig_f32 )zig_as_f32(0x1.ccccccp-1, zig_as_i32(0x3f666666)));
     t51 = t95;
     /* file:22:9 */
     zig_f32 const t96 = t51;
     /* file:22:33 */
     zig_S_rand_Random__343 const t97 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t98;
     t98 = t97;
     zig_S_rand_Random__343 const * const t99 = (zig_S_rand_Random__343 const * )&t98;
     zig_S_rand_Random__343 const t100 = (*t99);
     /* file:22:41 */
     zig_f32 const t101 = rand_Random_float__anon_695(t100);
     /* file:22:59 */
     zig_S_rand_Random__343 const t102 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t103;
     t103 = t102;
     zig_S_rand_Random__343 const * const t104 = (zig_S_rand_Random__343 const * )&t103;
     zig_S_rand_Random__343 const t105 = (*t104);
     /* file:22:67 */
     zig_f32 const t106 = rand_Random_float__anon_695(t105);
     zig_f32 const t107 = zig_sub_f32(t101, t106);
     zig_f32 const t108 = zig_add_f32(t96, t107);
     t51 = t108;
     /* file:24:9 */
     zig_f32 const t109 = t52;
     zig_f32 const t110 = zig_div_f32(t109, (zig_f32 )zig_as_f32(0x1p1, zig_as_i32(0x40000000)));
     t52 = t110;
     /* file:25:9 */
     zig_f32 const t111 = t52;
     zig_f32 const t112 = t61;
     zig_f32 const t113 = zig_div_f32(t112, (zig_f32 )zig_as_f32(0x1p2, zig_as_i32(0x40800000)));
     zig_f32 const t114 = zig_add_f32(t111, t113);
     t52 = t114;
     /* file:28:9 */
     zig_f32 const t115 = t61;
     zig_f32 const t116 = zig_mul_f32(t115, (zig_f32 )zig_as_f32(0x1.ccccccp-1, zig_as_i32(0x3f666666)));
     t61 = t116;
     /* file:29:9 */
     zig_f32 const t117 = t61;
     /* file:29:31 */
     zig_S_rand_Random__343 const t118 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t119;
     t119 = t118;
     zig_S_rand_Random__343 const * const t120 = (zig_S_rand_Random__343 const * )&t119;
     zig_S_rand_Random__343 const t121 = (*t120);
     /* file:29:39 */
     zig_f32 const t122 = rand_Random_float__anon_695(t121);
     /* file:29:57 */
     zig_S_rand_Random__343 const t123 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
     zig_S_rand_Random__343 t124;
     t124 = t123;
     zig_S_rand_Random__343 const * const t125 = (zig_S_rand_Random__343 const * )&t124;
     zig_S_rand_Random__343 const t126 = (*t125);
     /* file:29:65 */
     zig_f32 const t127 = rand_Random_float__anon_695(t126);
     zig_f32 const t128 = zig_sub_f32(t122, t127);
     zig_f32 const t129 = zig_add_f32(t117, t128);
     t61 = t129;
     /* file:31:9 */
     zig_f32 t130;
     /* file:31:46 */
     zig_usize const t131 = t62;
     zig_f32 const t132 = __floatunsisf(t131);
     zig_f32 const t133 = zig_mul_f32(t132, (zig_f32 )zig_as_f32(0x1.921fap1, zig_as_i32(0x40490fd0)));
     zig_f32 const t134 = t27;
     zig_f32 const t135 = zig_div_f32(t133, t134);
     /* dbg func:sin */
     /* var:value */
     /* file:2:5 */
     zig_f32 const t136 = zig_libc_name_f32(sin)(t135);
     /* file:2:5 */
     /* dbg func:create_vein */
     zig_f32 const t137 = zig_mul_f32(a0, t136);
     zig_f32 const t138 = zig_add_f32(t137, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000)));
     zig_f32 * const t139 = (zig_f32 * )&t130;
     (*t139) = t138;
     /* var:radius */
     /* file:33:9 */
     /* file:33:27 */
     zig_f32 const t140 = t0;
     zig_i32 const t141 = zig_wrap_i32(__fixsfsi(t140), zig_as_u8(32));
     zig_f32 const t142 = __floatsisf(t141);
     zig_f32 const t143 = zig_sub_f32(t140, t142);
     zig_bool const t144 = zig_lt_f32(t143, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
     zig_bool const t145 = zig_gt_f32(t143, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
     zig_bool const t146 = t144 & t145;
     {
      if (t146) {
       goto zig_block_3;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_vein__anon_706), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_3:;
     zig_f32 const t147 = t9;
     zig_i32 const t148 = zig_wrap_i32(__fixsfsi(t147), zig_as_u8(32));
     zig_f32 const t149 = __floatsisf(t148);
     zig_f32 const t150 = zig_sub_f32(t147, t149);
     zig_bool const t151 = zig_lt_f32(t150, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
     zig_bool const t152 = zig_gt_f32(t150, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
     zig_bool const t153 = t151 & t152;
     {
      if (t153) {
       goto zig_block_4;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_vein__anon_707), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_4:;
     zig_f32 const t154 = t18;
     zig_i32 const t155 = zig_wrap_i32(__fixsfsi(t154), zig_as_u8(32));
     zig_f32 const t156 = __floatsisf(t155);
     zig_f32 const t157 = zig_sub_f32(t154, t156);
     zig_bool const t158 = zig_lt_f32(t157, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
     zig_bool const t159 = zig_gt_f32(t157, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
     zig_bool const t160 = t158 & t159;
     {
      if (t160) {
       goto zig_block_5;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_vein__anon_708), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_5:;
     zig_f32 const t161 = t130;
     generator_fillOblateSpheroid(t141, t148, t155, t161, a1);
     /* file:15:44 */
     zig_usize const t162 = t62;
     zig_T_tuple_7busize_2c_20u1_7d t163;
     t163.f1 = zig_addo_u32(&t163.f0, t162, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t164 = t163.f1;
     zig_bool const t165 = t164 == zig_as_u8(0);
     {
      if (t165) {
       goto zig_block_6;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_vein__anon_709), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_6:;
     zig_usize const t166 = t163.f0;
     t62 = t166;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_void generator_create_flowers(zig_void) {
 /* file:2:5 */
 zig_u8 t0;
 /* file:2:37 */
 zig_S_rand_Random__343 const t1 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t2;
 t2 = t1;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:2:43 */
 zig_u8 const t5 = rand_Random_int__anon_710(t4);
 zig_u8 const t6 = zig_mod_u8(t5, zig_as_u8(2));
 zig_T_tuple_7bu8_2c_20u1_7d t7;
 t7.f1 = zig_addo_u8(&t7.f0, t6, zig_as_u8(37), zig_as_u8(8));
 zig_u8 const t8 = t7.f1;
 zig_bool const t9 = t8 == zig_as_u8(0);
 {
  if (t9) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_711), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_u8 const t10 = t7.f0;
 zig_u8 * const t11 = (zig_u8 * )&t0;
 (*t11) = t10;
 /* var:flowerType */
 /* file:3:5 */
 zig_usize t12;
 /* file:3:29 */
 zig_S_rand_Random__343 const t13 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t14;
 t14 = t13;
 zig_S_rand_Random__343 const * const t15 = (zig_S_rand_Random__343 const * )&t14;
 zig_S_rand_Random__343 const t16 = (*t15);
 /* file:3:35 */
 zig_usize const t17 = rand_Random_int__anon_712(t16);
 zig_usize const t18 = zig_mod_u32(t17, zig_as_u32(256));
 zig_usize * const t19 = (zig_usize * )&t12;
 (*t19) = t18;
 /* var:px */
 /* file:4:5 */
 zig_usize t20;
 /* file:4:29 */
 zig_S_rand_Random__343 const t21 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t22;
 t22 = t21;
 zig_S_rand_Random__343 const * const t23 = (zig_S_rand_Random__343 const * )&t22;
 zig_S_rand_Random__343 const t24 = (*t23);
 /* file:4:35 */
 zig_usize const t25 = rand_Random_int__anon_712(t24);
 zig_usize const t26 = zig_mod_u32(t25, zig_as_u32(256));
 zig_usize * const t27 = (zig_usize * )&t20;
 (*t27) = t26;
 /* var:pz */
 /* file:6:5 */
 zig_usize t28;
 t28 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:7:11 */
    zig_usize const t29 = t28;
    zig_u32 t30;
    memcpy(&t30, &t29, sizeof(zig_u32 ));
    t30 = zig_wrap_u32(t30, zig_as_u8(32));
    zig_bool const t31 = t30 < zig_as_u32(10);
    if (t31) {
     /* file:7:30 */
     /* file:9:5 */
     zig_usize t32;
     zig_usize const t33 = t12;
     zig_usize * const t34 = (zig_usize * )&t32;
     (*t34) = t33;
     /* var:fx */
     /* file:10:5 */
     zig_usize t35;
     zig_usize const t36 = t20;
     zig_usize * const t37 = (zig_usize * )&t35;
     (*t37) = t36;
     /* var:fz */
     /* file:12:5 */
     zig_usize t38;
     t38 = zig_as_u32(0);
     /* var:c */
     {
      while (zig_true) {
       {
        /* file:13:11 */
        zig_usize const t39 = t38;
        zig_u32 t40;
        memcpy(&t40, &t39, sizeof(zig_u32 ));
        t40 = zig_wrap_u32(t40, zig_as_u8(32));
        zig_bool const t41 = t40 < zig_as_u32(5);
        if (t41) {
         /* file:13:29 */
         /* file:14:9 */
         zig_usize const t42 = t32;
         /* file:14:30 */
         zig_S_rand_Random__343 const t43 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t44;
         t44 = t43;
         zig_S_rand_Random__343 const * const t45 = (zig_S_rand_Random__343 const * )&t44;
         zig_S_rand_Random__343 const t46 = (*t45);
         /* file:14:36 */
         zig_usize const t47 = rand_Random_int__anon_712(t46);
         zig_usize const t48 = zig_mod_u32(t47, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t49;
         t49.f1 = zig_addo_u32(&t49.f0, t42, t48, zig_as_u8(32));
         zig_u8 const t50 = t49.f1;
         zig_bool const t51 = t50 == zig_as_u8(0);
         {
          if (t51) {
           goto zig_block_5;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_713), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_5:;
         zig_usize const t52 = t49.f0;
         t32 = t52;
         /* file:16:9 */
         zig_usize t53;
         /* file:16:34 */
         zig_S_rand_Random__343 const t54 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t55;
         t55 = t54;
         zig_S_rand_Random__343 const * const t56 = (zig_S_rand_Random__343 const * )&t55;
         zig_S_rand_Random__343 const t57 = (*t56);
         /* file:16:40 */
         zig_usize const t58 = rand_Random_int__anon_712(t57);
         zig_usize const t59 = zig_mod_u32(t58, zig_as_u32(6));
         zig_usize * const t60 = (zig_usize * )&t53;
         (*t60) = t59;
         /* var:sub */
         /* file:17:12 */
         {
          zig_usize const t61 = t32;
          zig_usize const t62 = t53;
          zig_u32 t63;
          memcpy(&t63, &t61, sizeof(zig_u32 ));
          t63 = zig_wrap_u32(t63, zig_as_u8(32));
          zig_u32 t64;
          memcpy(&t64, &t62, sizeof(zig_u32 ));
          t64 = zig_wrap_u32(t64, zig_as_u8(32));
          zig_bool const t65 = t63 > t64;
          if (t65) {
           /* file:18:13 */
           zig_usize const t66 = t32;
           zig_usize const t67 = t53;
           zig_T_tuple_7busize_2c_20u1_7d t68;
           t68.f1 = zig_subo_u32(&t68.f0, t66, t67, zig_as_u8(32));
           zig_u8 const t69 = t68.f1;
           zig_bool const t70 = t69 == zig_as_u8(0);
           {
            if (t70) {
             goto zig_block_7;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_714), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_7:;
           zig_usize const t71 = t68.f0;
           t32 = t71;
           goto zig_block_6;
          } else {
           goto zig_block_6;
          }
         }
         zig_block_6:;
         /* file:20:9 */
         /* file:20:30 */
         zig_S_rand_Random__343 const t72 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t73;
         t73 = t72;
         zig_S_rand_Random__343 const * const t74 = (zig_S_rand_Random__343 const * )&t73;
         zig_S_rand_Random__343 const t75 = (*t74);
         /* file:20:36 */
         zig_usize const t76 = rand_Random_int__anon_712(t75);
         zig_usize const t77 = zig_mod_u32(t76, zig_as_u32(6));
         t53 = t77;
         /* file:21:9 */
         zig_usize const t78 = t35;
         /* file:21:30 */
         zig_S_rand_Random__343 const t79 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t80;
         t80 = t79;
         zig_S_rand_Random__343 const * const t81 = (zig_S_rand_Random__343 const * )&t80;
         zig_S_rand_Random__343 const t82 = (*t81);
         /* file:21:36 */
         zig_usize const t83 = rand_Random_int__anon_712(t82);
         zig_usize const t84 = zig_mod_u32(t83, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t85;
         t85.f1 = zig_addo_u32(&t85.f0, t78, t84, zig_as_u8(32));
         zig_u8 const t86 = t85.f1;
         zig_bool const t87 = t86 == zig_as_u8(0);
         {
          if (t87) {
           goto zig_block_8;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_715), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_8:;
         zig_usize const t88 = t85.f0;
         t35 = t88;
         /* file:22:12 */
         {
          zig_usize const t89 = t35;
          zig_usize const t90 = t53;
          zig_u32 t91;
          memcpy(&t91, &t89, sizeof(zig_u32 ));
          t91 = zig_wrap_u32(t91, zig_as_u8(32));
          zig_u32 t92;
          memcpy(&t92, &t90, sizeof(zig_u32 ));
          t92 = zig_wrap_u32(t92, zig_as_u8(32));
          zig_bool const t93 = t91 > t92;
          if (t93) {
           /* file:23:13 */
           zig_usize const t94 = t35;
           zig_usize const t95 = t53;
           zig_T_tuple_7busize_2c_20u1_7d t96;
           t96.f1 = zig_subo_u32(&t96.f0, t94, t95, zig_as_u8(32));
           zig_u8 const t97 = t96.f1;
           zig_bool const t98 = t97 == zig_as_u8(0);
           {
            if (t98) {
             goto zig_block_10;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_716), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_10:;
           zig_usize const t99 = t96.f0;
           t35 = t99;
           goto zig_block_9;
          } else {
           goto zig_block_9;
          }
         }
         zig_block_9:;
         /* file:25:12 */
         {
          zig_usize const t100 = t32;
          zig_u32 t101;
          memcpy(&t101, &t100, sizeof(zig_u32 ));
          t101 = zig_wrap_u32(t101, zig_as_u8(32));
          zig_bool const t102 = t101 < zig_as_u32(256);
          zig_bool t103;
          {
           if (t102) {
            t103 = zig_true;
            goto zig_block_12;
           } else {
            t103 = zig_false;
            goto zig_block_12;
           }
          }
          zig_block_12:;
          zig_bool t104;
          {
           if (t103) {
            zig_usize const t105 = t35;
            zig_u32 t106;
            memcpy(&t106, &t105, sizeof(zig_u32 ));
            t106 = zig_wrap_u32(t106, zig_as_u8(32));
            zig_bool const t107 = t106 < zig_as_u32(256);
            t104 = t107;
            goto zig_block_13;
           } else {
            t104 = zig_false;
            goto zig_block_13;
           }
          }
          zig_block_13:;
          if (t104) {
           /* file:26:13 */
           zig_i32 t108;
           zig_i32 t109[zig_as_u32(65536)];
           memcpy(t109, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
           zig_usize const t110 = t32;
           zig_usize const t111 = t35;
           zig_T_tuple_7busize_2c_20u1_7d t112;
           t112.f1 = zig_mulo_u32(&t112.f0, t111, zig_as_u32(256), zig_as_u8(32));
           zig_u8 const t113 = t112.f1;
           zig_bool const t114 = t113 == zig_as_u8(0);
           {
            if (t114) {
             goto zig_block_14;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_717), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_14:;
           zig_usize const t115 = t112.f0;
           zig_T_tuple_7busize_2c_20u1_7d t116;
           t116.f1 = zig_addo_u32(&t116.f0, t110, t115, zig_as_u8(32));
           zig_u8 const t117 = t116.f1;
           zig_bool const t118 = t117 == zig_as_u8(0);
           {
            if (t118) {
             goto zig_block_15;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_718), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_15:;
           zig_usize const t119 = t116.f0;
           zig_usize const t120 = (zig_usize )t119;
           zig_bool const t121 = t120 < zig_as_u32(65536);
           {
            if (t121) {
             goto zig_block_16;
            } else {
             zig_breakpoint();
             zig_unreachable();
            }
           }
           zig_block_16:;
           zig_i32 const t122 = t109[t120];
           zig_T_tuple_7bi32_2c_20u1_7d t123;
           t123.f1 = zig_addo_i32(&t123.f0, t122, zig_as_i32(1), zig_as_u8(32));
           zig_u8 const t124 = t123.f1;
           zig_bool const t125 = t124 == zig_as_u8(0);
           {
            if (t125) {
             goto zig_block_17;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_719), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_17:;
           zig_i32 const t126 = t123.f0;
           zig_i32 * const t127 = (zig_i32 * )&t108;
           (*t127) = t126;
           /* var:fy */
           /* file:28:13 */
           zig_u8 t128;
           zig_u8 * const t129 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           /* file:28:39 */
           zig_usize const t130 = t32;
           zig_u32 const t131 = (zig_u32 )t130;
           zig_i32 const t132 = t108;
           zig_bool const t133 = t132 >= zig_as_i32(0);
           {
            if (t133) {
             goto zig_block_18;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_720), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_18:;
           zig_u32 const t134 = (zig_u32 )t132;
           zig_usize const t135 = t35;
           zig_u32 const t136 = (zig_u32 )t135;
           zig_usize const t137 = generator_getIdx(t131, t134, t136);
           zig_u8 const t138 = t129[t137];
           zig_u8 * const t139 = (zig_u8 * )&t128;
           (*t139) = t138;
           /* var:blk */
           /* file:29:13 */
           zig_u8 t140;
           zig_u8 * const t141 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           /* file:29:40 */
           zig_usize const t142 = t32;
           zig_u32 const t143 = (zig_u32 )t142;
           zig_i32 const t144 = t108;
           zig_bool const t145 = t144 >= zig_as_i32(0);
           {
            if (t145) {
             goto zig_block_19;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_721), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_19:;
           zig_u32 const t146 = (zig_u32 )t144;
           zig_T_tuple_7bu32_2c_20u1_7d t147;
           t147.f1 = zig_subo_u32(&t147.f0, t146, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t148 = t147.f1;
           zig_bool const t149 = t148 == zig_as_u8(0);
           {
            if (t149) {
             goto zig_block_20;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_722), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_20:;
           zig_u32 const t150 = t147.f0;
           zig_usize const t151 = t35;
           zig_u32 const t152 = (zig_u32 )t151;
           zig_usize const t153 = generator_getIdx(t143, t150, t152);
           zig_u8 const t154 = t141[t153];
           zig_u8 * const t155 = (zig_u8 * )&t140;
           (*t155) = t154;
           /* var:blkB */
           /* file:31:16 */
           {
            zig_u8 const t156 = t128;
            zig_bool const t157 = t156 == zig_as_u8(0);
            zig_bool t158;
            {
             if (t157) {
              zig_u8 const t159 = t140;
              zig_bool const t160 = t159 == zig_as_u8(2);
              t158 = t160;
              goto zig_block_22;
             } else {
              t158 = zig_false;
              goto zig_block_22;
             }
            }
            zig_block_22:;
            if (t158) {
             /* file:32:17 */
             /* file:32:33 */
             zig_usize const t161 = t32;
             zig_u32 const t162 = (zig_u32 )t161;
             zig_i32 const t163 = t108;
             zig_bool const t164 = t163 >= zig_as_i32(0);
             {
              if (t164) {
               goto zig_block_23;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_723), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_23:;
             zig_u32 const t165 = (zig_u32 )t163;
             zig_usize const t166 = t35;
             zig_u32 const t167 = (zig_u32 )t166;
             zig_usize const t168 = generator_getIdx(t162, t165, t167);
             zig_u8 * const t169 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t170 = &(t169)[t168];
             zig_u8 const t171 = t0;
             (*t170) = t171;
             goto zig_block_21;
            } else {
             goto zig_block_21;
            }
           }
           zig_block_21:;
           goto zig_block_11;
          } else {
           goto zig_block_11;
          }
         }
         zig_block_11:;
         /* file:13:21 */
         zig_usize const t172 = t38;
         zig_T_tuple_7busize_2c_20u1_7d t173;
         t173.f1 = zig_addo_u32(&t173.f0, t172, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t174 = t173.f1;
         zig_bool const t175 = t174 == zig_as_u8(0);
         {
          if (t175) {
           goto zig_block_24;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_724), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_24:;
         zig_usize const t176 = t173.f0;
         t38 = t176;
         goto zig_block_4;
        } else {
         goto zig_block_3;
        }
       }
       zig_block_4:;
      }
     }
     zig_block_3:;
     /* file:7:22 */
     zig_usize const t177 = t28;
     zig_T_tuple_7busize_2c_20u1_7d t178;
     t178.f1 = zig_addo_u32(&t178.f0, t177, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t179 = t178.f1;
     zig_bool const t180 = t179 == zig_as_u8(0);
     {
      if (t180) {
       goto zig_block_25;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_flowers__anon_725), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_25:;
     zig_usize const t181 = t178.f0;
     t28 = t181;
     goto zig_block_2;
    } else {
     goto zig_block_1;
    }
   }
   zig_block_2:;
  }
 }
 zig_block_1:;
 return;
}

static zig_void generator_create_mushrooms(zig_void) {
 /* file:2:5 */
 zig_u8 t0;
 /* file:2:35 */
 zig_S_rand_Random__343 const t1 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t2;
 t2 = t1;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:2:41 */
 zig_u8 const t5 = rand_Random_int__anon_710(t4);
 zig_u8 const t6 = zig_mod_u8(t5, zig_as_u8(2));
 zig_T_tuple_7bu8_2c_20u1_7d t7;
 t7.f1 = zig_addo_u8(&t7.f0, t6, zig_as_u8(39), zig_as_u8(8));
 zig_u8 const t8 = t7.f1;
 zig_bool const t9 = t8 == zig_as_u8(0);
 {
  if (t9) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_726), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_u8 const t10 = t7.f0;
 zig_u8 * const t11 = (zig_u8 * )&t0;
 (*t11) = t10;
 /* var:mushType */
 /* file:3:5 */
 zig_usize t12;
 /* file:3:29 */
 zig_S_rand_Random__343 const t13 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t14;
 t14 = t13;
 zig_S_rand_Random__343 const * const t15 = (zig_S_rand_Random__343 const * )&t14;
 zig_S_rand_Random__343 const t16 = (*t15);
 /* file:3:35 */
 zig_usize const t17 = rand_Random_int__anon_712(t16);
 zig_usize const t18 = zig_mod_u32(t17, zig_as_u32(256));
 zig_usize * const t19 = (zig_usize * )&t12;
 (*t19) = t18;
 /* var:px */
 /* file:4:5 */
 zig_usize t20;
 /* file:4:29 */
 zig_S_rand_Random__343 const t21 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t22;
 t22 = t21;
 zig_S_rand_Random__343 const * const t23 = (zig_S_rand_Random__343 const * )&t22;
 zig_S_rand_Random__343 const t24 = (*t23);
 /* file:4:35 */
 zig_usize const t25 = rand_Random_int__anon_712(t24);
 zig_usize const t26 = zig_mod_u32(t25, zig_as_u32(64));
 zig_usize * const t27 = (zig_usize * )&t20;
 (*t27) = t26;
 /* var:py */
 /* file:5:5 */
 zig_usize t28;
 /* file:5:29 */
 zig_S_rand_Random__343 const t29 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t30;
 t30 = t29;
 zig_S_rand_Random__343 const * const t31 = (zig_S_rand_Random__343 const * )&t30;
 zig_S_rand_Random__343 const t32 = (*t31);
 /* file:5:35 */
 zig_usize const t33 = rand_Random_int__anon_712(t32);
 zig_usize const t34 = zig_mod_u32(t33, zig_as_u32(256));
 zig_usize * const t35 = (zig_usize * )&t28;
 (*t35) = t34;
 /* var:pz */
 /* file:7:5 */
 zig_usize t36;
 t36 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:8:11 */
    zig_usize const t37 = t36;
    zig_u32 t38;
    memcpy(&t38, &t37, sizeof(zig_u32 ));
    t38 = zig_wrap_u32(t38, zig_as_u8(32));
    zig_bool const t39 = t38 < zig_as_u32(20);
    if (t39) {
     /* file:8:30 */
     /* file:10:5 */
     zig_usize t40;
     zig_usize const t41 = t12;
     zig_usize * const t42 = (zig_usize * )&t40;
     (*t42) = t41;
     /* var:fx */
     /* file:11:5 */
     zig_usize t43;
     zig_usize const t44 = t20;
     zig_usize * const t45 = (zig_usize * )&t43;
     (*t45) = t44;
     /* var:fy */
     /* file:12:5 */
     zig_usize t46;
     zig_usize const t47 = t28;
     zig_usize * const t48 = (zig_usize * )&t46;
     (*t48) = t47;
     /* var:fz */
     /* file:14:5 */
     zig_usize t49;
     t49 = zig_as_u32(0);
     /* var:c */
     {
      while (zig_true) {
       {
        /* file:15:11 */
        zig_usize const t50 = t49;
        zig_u32 t51;
        memcpy(&t51, &t50, sizeof(zig_u32 ));
        t51 = zig_wrap_u32(t51, zig_as_u8(32));
        zig_bool const t52 = t51 < zig_as_u32(5);
        if (t52) {
         /* file:15:29 */
         /* file:16:9 */
         zig_usize const t53 = t40;
         /* file:16:30 */
         zig_S_rand_Random__343 const t54 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t55;
         t55 = t54;
         zig_S_rand_Random__343 const * const t56 = (zig_S_rand_Random__343 const * )&t55;
         zig_S_rand_Random__343 const t57 = (*t56);
         /* file:16:36 */
         zig_usize const t58 = rand_Random_int__anon_712(t57);
         zig_usize const t59 = zig_mod_u32(t58, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t60;
         t60.f1 = zig_addo_u32(&t60.f0, t53, t59, zig_as_u8(32));
         zig_u8 const t61 = t60.f1;
         zig_bool const t62 = t61 == zig_as_u8(0);
         {
          if (t62) {
           goto zig_block_5;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_727), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_5:;
         zig_usize const t63 = t60.f0;
         t40 = t63;
         /* file:18:9 */
         zig_usize t64;
         /* file:18:34 */
         zig_S_rand_Random__343 const t65 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t66;
         t66 = t65;
         zig_S_rand_Random__343 const * const t67 = (zig_S_rand_Random__343 const * )&t66;
         zig_S_rand_Random__343 const t68 = (*t67);
         /* file:18:40 */
         zig_usize const t69 = rand_Random_int__anon_712(t68);
         zig_usize const t70 = zig_mod_u32(t69, zig_as_u32(6));
         zig_usize * const t71 = (zig_usize * )&t64;
         (*t71) = t70;
         /* var:sub */
         /* file:19:12 */
         {
          zig_usize const t72 = t40;
          zig_usize const t73 = t64;
          zig_u32 t74;
          memcpy(&t74, &t72, sizeof(zig_u32 ));
          t74 = zig_wrap_u32(t74, zig_as_u8(32));
          zig_u32 t75;
          memcpy(&t75, &t73, sizeof(zig_u32 ));
          t75 = zig_wrap_u32(t75, zig_as_u8(32));
          zig_bool const t76 = t74 > t75;
          if (t76) {
           /* file:20:13 */
           zig_usize const t77 = t40;
           zig_usize const t78 = t64;
           zig_T_tuple_7busize_2c_20u1_7d t79;
           t79.f1 = zig_subo_u32(&t79.f0, t77, t78, zig_as_u8(32));
           zig_u8 const t80 = t79.f1;
           zig_bool const t81 = t80 == zig_as_u8(0);
           {
            if (t81) {
             goto zig_block_7;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_728), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_7:;
           zig_usize const t82 = t79.f0;
           t40 = t82;
           goto zig_block_6;
          } else {
           goto zig_block_6;
          }
         }
         zig_block_6:;
         /* file:22:9 */
         /* file:22:30 */
         zig_S_rand_Random__343 const t83 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t84;
         t84 = t83;
         zig_S_rand_Random__343 const * const t85 = (zig_S_rand_Random__343 const * )&t84;
         zig_S_rand_Random__343 const t86 = (*t85);
         /* file:22:36 */
         zig_usize const t87 = rand_Random_int__anon_712(t86);
         zig_usize const t88 = zig_mod_u32(t87, zig_as_u32(6));
         t64 = t88;
         /* file:23:9 */
         zig_usize const t89 = t46;
         /* file:23:30 */
         zig_S_rand_Random__343 const t90 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t91;
         t91 = t90;
         zig_S_rand_Random__343 const * const t92 = (zig_S_rand_Random__343 const * )&t91;
         zig_S_rand_Random__343 const t93 = (*t92);
         /* file:23:36 */
         zig_usize const t94 = rand_Random_int__anon_712(t93);
         zig_usize const t95 = zig_mod_u32(t94, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t96;
         t96.f1 = zig_addo_u32(&t96.f0, t89, t95, zig_as_u8(32));
         zig_u8 const t97 = t96.f1;
         zig_bool const t98 = t97 == zig_as_u8(0);
         {
          if (t98) {
           goto zig_block_8;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_729), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_8:;
         zig_usize const t99 = t96.f0;
         t46 = t99;
         /* file:24:12 */
         {
          zig_usize const t100 = t46;
          zig_usize const t101 = t64;
          zig_u32 t102;
          memcpy(&t102, &t100, sizeof(zig_u32 ));
          t102 = zig_wrap_u32(t102, zig_as_u8(32));
          zig_u32 t103;
          memcpy(&t103, &t101, sizeof(zig_u32 ));
          t103 = zig_wrap_u32(t103, zig_as_u8(32));
          zig_bool const t104 = t102 > t103;
          if (t104) {
           /* file:25:13 */
           zig_usize const t105 = t46;
           zig_usize const t106 = t64;
           zig_T_tuple_7busize_2c_20u1_7d t107;
           t107.f1 = zig_subo_u32(&t107.f0, t105, t106, zig_as_u8(32));
           zig_u8 const t108 = t107.f1;
           zig_bool const t109 = t108 == zig_as_u8(0);
           {
            if (t109) {
             goto zig_block_10;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_730), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_10:;
           zig_usize const t110 = t107.f0;
           t46 = t110;
           goto zig_block_9;
          } else {
           goto zig_block_9;
          }
         }
         zig_block_9:;
         /* file:27:9 */
         /* file:27:30 */
         zig_S_rand_Random__343 const t111 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t112;
         t112 = t111;
         zig_S_rand_Random__343 const * const t113 = (zig_S_rand_Random__343 const * )&t112;
         zig_S_rand_Random__343 const t114 = (*t113);
         /* file:27:36 */
         zig_usize const t115 = rand_Random_int__anon_712(t114);
         zig_usize const t116 = zig_mod_u32(t115, zig_as_u32(2));
         t64 = t116;
         /* file:28:9 */
         zig_usize const t117 = t43;
         /* file:28:30 */
         zig_S_rand_Random__343 const t118 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t119;
         t119 = t118;
         zig_S_rand_Random__343 const * const t120 = (zig_S_rand_Random__343 const * )&t119;
         zig_S_rand_Random__343 const t121 = (*t120);
         /* file:28:36 */
         zig_usize const t122 = rand_Random_int__anon_712(t121);
         zig_usize const t123 = zig_mod_u32(t122, zig_as_u32(2));
         zig_T_tuple_7busize_2c_20u1_7d t124;
         t124.f1 = zig_addo_u32(&t124.f0, t117, t123, zig_as_u8(32));
         zig_u8 const t125 = t124.f1;
         zig_bool const t126 = t125 == zig_as_u8(0);
         {
          if (t126) {
           goto zig_block_11;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_731), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_11:;
         zig_usize const t127 = t124.f0;
         t43 = t127;
         /* file:29:12 */
         {
          zig_usize const t128 = t43;
          zig_usize const t129 = t64;
          zig_u32 t130;
          memcpy(&t130, &t128, sizeof(zig_u32 ));
          t130 = zig_wrap_u32(t130, zig_as_u8(32));
          zig_u32 t131;
          memcpy(&t131, &t129, sizeof(zig_u32 ));
          t131 = zig_wrap_u32(t131, zig_as_u8(32));
          zig_bool const t132 = t130 > t131;
          if (t132) {
           /* file:30:13 */
           zig_usize const t133 = t43;
           zig_usize const t134 = t64;
           zig_T_tuple_7busize_2c_20u1_7d t135;
           t135.f1 = zig_subo_u32(&t135.f0, t133, t134, zig_as_u8(32));
           zig_u8 const t136 = t135.f1;
           zig_bool const t137 = t136 == zig_as_u8(0);
           {
            if (t137) {
             goto zig_block_13;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_732), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_13:;
           zig_usize const t138 = t135.f0;
           t43 = t138;
           goto zig_block_12;
          } else {
           goto zig_block_12;
          }
         }
         zig_block_12:;
         /* file:32:12 */
         {
          zig_usize const t139 = t40;
          zig_u32 t140;
          memcpy(&t140, &t139, sizeof(zig_u32 ));
          t140 = zig_wrap_u32(t140, zig_as_u8(32));
          zig_bool const t141 = t140 < zig_as_u32(256);
          zig_bool t142;
          {
           if (t141) {
            t142 = zig_true;
            goto zig_block_15;
           } else {
            t142 = zig_false;
            goto zig_block_15;
           }
          }
          zig_block_15:;
          zig_bool t143;
          {
           if (t142) {
            zig_usize const t144 = t46;
            zig_u32 t145;
            memcpy(&t145, &t144, sizeof(zig_u32 ));
            t145 = zig_wrap_u32(t145, zig_as_u8(32));
            zig_bool const t146 = t145 < zig_as_u32(256);
            t143 = t146;
            goto zig_block_16;
           } else {
            t143 = zig_false;
            goto zig_block_16;
           }
          }
          zig_block_16:;
          zig_bool t147;
          {
           if (t143) {
            zig_usize const t148 = t43;
            zig_u32 t149;
            memcpy(&t149, &t148, sizeof(zig_u32 ));
            t149 = zig_wrap_u32(t149, zig_as_u8(32));
            zig_bool const t150 = t149 > zig_as_u32(0);
            t147 = t150;
            goto zig_block_17;
           } else {
            t147 = zig_false;
            goto zig_block_17;
           }
          }
          zig_block_17:;
          zig_bool t151;
          {
           if (t147) {
            zig_usize const t152 = t43;
            zig_u32 t153;
            memcpy(&t153, &t152, sizeof(zig_u32 ));
            t153 = zig_wrap_u32(t153, zig_as_u8(32));
            zig_bool const t154 = t153 < zig_as_u32(64);
            t151 = t154;
            goto zig_block_18;
           } else {
            t151 = zig_false;
            goto zig_block_18;
           }
          }
          zig_block_18:;
          if (t151) {
           /* file:34:13 */
           zig_u8 t155;
           zig_u8 * const t156 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           /* file:34:39 */
           zig_usize const t157 = t40;
           zig_u32 const t158 = (zig_u32 )t157;
           zig_usize const t159 = t43;
           zig_u32 const t160 = (zig_u32 )t159;
           zig_usize const t161 = t46;
           zig_u32 const t162 = (zig_u32 )t161;
           zig_usize const t163 = generator_getIdx(t158, t160, t162);
           zig_u8 const t164 = t156[t163];
           zig_u8 * const t165 = (zig_u8 * )&t155;
           (*t165) = t164;
           /* var:blk */
           /* file:36:13 */
           zig_u8 t166;
           zig_u8 * const t167 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           /* file:36:40 */
           zig_usize const t168 = t40;
           zig_u32 const t169 = (zig_u32 )t168;
           zig_usize const t170 = t43;
           zig_u32 const t171 = (zig_u32 )t170;
           zig_T_tuple_7bu32_2c_20u1_7d t172;
           t172.f1 = zig_subo_u32(&t172.f0, t171, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t173 = t172.f1;
           zig_bool const t174 = t173 == zig_as_u8(0);
           {
            if (t174) {
             goto zig_block_19;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_733), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_19:;
           zig_u32 const t175 = t172.f0;
           zig_usize const t176 = t46;
           zig_u32 const t177 = (zig_u32 )t176;
           zig_usize const t178 = generator_getIdx(t169, t175, t177);
           zig_u8 const t179 = t167[t178];
           zig_u8 * const t180 = (zig_u8 * )&t166;
           (*t180) = t179;
           /* var:blkB */
           /* file:38:16 */
           {
            zig_u8 const t181 = t155;
            zig_bool const t182 = t181 == zig_as_u8(0);
            zig_bool t183;
            {
             if (t182) {
              zig_u8 const t184 = t166;
              zig_bool const t185 = t184 == zig_as_u8(1);
              t183 = t185;
              goto zig_block_21;
             } else {
              t183 = zig_false;
              goto zig_block_21;
             }
            }
            zig_block_21:;
            if (t183) {
             /* file:39:17 */
             /* file:39:33 */
             zig_usize const t186 = t40;
             zig_u32 const t187 = (zig_u32 )t186;
             zig_usize const t188 = t43;
             zig_u32 const t189 = (zig_u32 )t188;
             zig_usize const t190 = t46;
             zig_u32 const t191 = (zig_u32 )t190;
             zig_usize const t192 = generator_getIdx(t187, t189, t191);
             zig_u8 * const t193 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t194 = &(t193)[t192];
             zig_u8 const t195 = t0;
             (*t194) = t195;
             goto zig_block_20;
            } else {
             goto zig_block_20;
            }
           }
           zig_block_20:;
           goto zig_block_14;
          } else {
           goto zig_block_14;
          }
         }
         zig_block_14:;
         /* file:15:21 */
         zig_usize const t196 = t49;
         zig_T_tuple_7busize_2c_20u1_7d t197;
         t197.f1 = zig_addo_u32(&t197.f0, t196, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t198 = t197.f1;
         zig_bool const t199 = t198 == zig_as_u8(0);
         {
          if (t199) {
           goto zig_block_22;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_734), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_22:;
         zig_usize const t200 = t197.f0;
         t49 = t200;
         goto zig_block_4;
        } else {
         goto zig_block_3;
        }
       }
       zig_block_4:;
      }
     }
     zig_block_3:;
     /* file:8:22 */
     zig_usize const t201 = t36;
     zig_T_tuple_7busize_2c_20u1_7d t202;
     t202.f1 = zig_addo_u32(&t202.f0, t201, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t203 = t202.f1;
     zig_bool const t204 = t203 == zig_as_u8(0);
     {
      if (t204) {
       goto zig_block_23;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_mushrooms__anon_735), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_23:;
     zig_usize const t205 = t202.f0;
     t36 = t205;
     goto zig_block_2;
    } else {
     goto zig_block_1;
    }
   }
   zig_block_2:;
  }
 }
 zig_block_1:;
 return;
}

static zig_void generator_create_tree(zig_void) {
 /* file:2:5 */
 zig_usize t0;
 /* file:2:29 */
 zig_S_rand_Random__343 const t1 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t2;
 t2 = t1;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:2:35 */
 zig_usize const t5 = rand_Random_int__anon_712(t4);
 zig_usize const t6 = zig_mod_u32(t5, zig_as_u32(256));
 zig_usize * const t7 = (zig_usize * )&t0;
 (*t7) = t6;
 /* var:px */
 /* file:3:5 */
 zig_usize t8;
 /* file:3:29 */
 zig_S_rand_Random__343 const t9 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
 zig_S_rand_Random__343 t10;
 t10 = t9;
 zig_S_rand_Random__343 const * const t11 = (zig_S_rand_Random__343 const * )&t10;
 zig_S_rand_Random__343 const t12 = (*t11);
 /* file:3:35 */
 zig_usize const t13 = rand_Random_int__anon_712(t12);
 zig_usize const t14 = zig_mod_u32(t13, zig_as_u32(256));
 zig_usize * const t15 = (zig_usize * )&t8;
 (*t15) = t14;
 /* var:pz */
 /* file:5:5 */
 zig_usize t16;
 t16 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:6:11 */
    zig_usize const t17 = t16;
    zig_u32 t18;
    memcpy(&t18, &t17, sizeof(zig_u32 ));
    t18 = zig_wrap_u32(t18, zig_as_u8(32));
    zig_bool const t19 = t18 < zig_as_u32(20);
    if (t19) {
     /* file:6:30 */
     /* file:7:9 */
     zig_usize t20;
     zig_usize const t21 = t0;
     zig_usize * const t22 = (zig_usize * )&t20;
     (*t22) = t21;
     /* var:tx */
     /* file:8:9 */
     zig_usize t23;
     zig_usize const t24 = t8;
     zig_usize * const t25 = (zig_usize * )&t23;
     (*t25) = t24;
     /* var:tz */
     /* file:10:9 */
     zig_usize t26;
     t26 = zig_as_u32(0);
     /* var:c */
     {
      while (zig_true) {
       {
        /* file:11:15 */
        zig_usize const t27 = t26;
        zig_u32 t28;
        memcpy(&t28, &t27, sizeof(zig_u32 ));
        t28 = zig_wrap_u32(t28, zig_as_u8(32));
        zig_bool const t29 = t28 < zig_as_u32(20);
        if (t29) {
         /* file:11:34 */
         /* file:12:13 */
         zig_usize const t30 = t20;
         /* file:12:34 */
         zig_S_rand_Random__343 const t31 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t32;
         t32 = t31;
         zig_S_rand_Random__343 const * const t33 = (zig_S_rand_Random__343 const * )&t32;
         zig_S_rand_Random__343 const t34 = (*t33);
         /* file:12:40 */
         zig_usize const t35 = rand_Random_int__anon_712(t34);
         zig_usize const t36 = zig_mod_u32(t35, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t37;
         t37.f1 = zig_addo_u32(&t37.f0, t30, t36, zig_as_u8(32));
         zig_u8 const t38 = t37.f1;
         zig_bool const t39 = t38 == zig_as_u8(0);
         {
          if (t39) {
           goto zig_block_4;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_736), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_4:;
         zig_usize const t40 = t37.f0;
         t20 = t40;
         /* file:14:13 */
         zig_usize t41;
         /* file:14:38 */
         zig_S_rand_Random__343 const t42 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t43;
         t43 = t42;
         zig_S_rand_Random__343 const * const t44 = (zig_S_rand_Random__343 const * )&t43;
         zig_S_rand_Random__343 const t45 = (*t44);
         /* file:14:44 */
         zig_usize const t46 = rand_Random_int__anon_712(t45);
         zig_usize const t47 = zig_mod_u32(t46, zig_as_u32(6));
         zig_usize * const t48 = (zig_usize * )&t41;
         (*t48) = t47;
         /* var:sub */
         /* file:15:16 */
         {
          zig_usize const t49 = t20;
          zig_usize const t50 = t41;
          zig_u32 t51;
          memcpy(&t51, &t49, sizeof(zig_u32 ));
          t51 = zig_wrap_u32(t51, zig_as_u8(32));
          zig_u32 t52;
          memcpy(&t52, &t50, sizeof(zig_u32 ));
          t52 = zig_wrap_u32(t52, zig_as_u8(32));
          zig_bool const t53 = t51 > t52;
          if (t53) {
           /* file:16:17 */
           zig_usize const t54 = t20;
           zig_usize const t55 = t41;
           zig_T_tuple_7busize_2c_20u1_7d t56;
           t56.f1 = zig_subo_u32(&t56.f0, t54, t55, zig_as_u8(32));
           zig_u8 const t57 = t56.f1;
           zig_bool const t58 = t57 == zig_as_u8(0);
           {
            if (t58) {
             goto zig_block_6;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_737), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_6:;
           zig_usize const t59 = t56.f0;
           t20 = t59;
           goto zig_block_5;
          } else {
           goto zig_block_5;
          }
         }
         zig_block_5:;
         /* file:18:13 */
         /* file:18:34 */
         zig_S_rand_Random__343 const t60 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t61;
         t61 = t60;
         zig_S_rand_Random__343 const * const t62 = (zig_S_rand_Random__343 const * )&t61;
         zig_S_rand_Random__343 const t63 = (*t62);
         /* file:18:40 */
         zig_usize const t64 = rand_Random_int__anon_712(t63);
         zig_usize const t65 = zig_mod_u32(t64, zig_as_u32(6));
         t41 = t65;
         /* file:19:13 */
         zig_usize const t66 = t23;
         /* file:19:34 */
         zig_S_rand_Random__343 const t67 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
         zig_S_rand_Random__343 t68;
         t68 = t67;
         zig_S_rand_Random__343 const * const t69 = (zig_S_rand_Random__343 const * )&t68;
         zig_S_rand_Random__343 const t70 = (*t69);
         /* file:19:40 */
         zig_usize const t71 = rand_Random_int__anon_712(t70);
         zig_usize const t72 = zig_mod_u32(t71, zig_as_u32(6));
         zig_T_tuple_7busize_2c_20u1_7d t73;
         t73.f1 = zig_addo_u32(&t73.f0, t66, t72, zig_as_u8(32));
         zig_u8 const t74 = t73.f1;
         zig_bool const t75 = t74 == zig_as_u8(0);
         {
          if (t75) {
           goto zig_block_7;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_738), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_7:;
         zig_usize const t76 = t73.f0;
         t23 = t76;
         /* file:20:16 */
         {
          zig_usize const t77 = t23;
          zig_usize const t78 = t41;
          zig_u32 t79;
          memcpy(&t79, &t77, sizeof(zig_u32 ));
          t79 = zig_wrap_u32(t79, zig_as_u8(32));
          zig_u32 t80;
          memcpy(&t80, &t78, sizeof(zig_u32 ));
          t80 = zig_wrap_u32(t80, zig_as_u8(32));
          zig_bool const t81 = t79 > t80;
          if (t81) {
           /* file:21:17 */
           zig_usize const t82 = t23;
           zig_usize const t83 = t41;
           zig_T_tuple_7busize_2c_20u1_7d t84;
           t84.f1 = zig_subo_u32(&t84.f0, t82, t83, zig_as_u8(32));
           zig_u8 const t85 = t84.f1;
           zig_bool const t86 = t85 == zig_as_u8(0);
           {
            if (t86) {
             goto zig_block_9;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_739), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_9:;
           zig_usize const t87 = t84.f0;
           t23 = t87;
           goto zig_block_8;
          } else {
           goto zig_block_8;
          }
         }
         zig_block_8:;
         /* file:23:16 */
         {
          zig_usize const t88 = t20;
          zig_u32 t89;
          memcpy(&t89, &t88, sizeof(zig_u32 ));
          t89 = zig_wrap_u32(t89, zig_as_u8(32));
          zig_bool const t90 = t89 < zig_as_u32(256);
          zig_bool t91;
          {
           if (t90) {
            t91 = zig_true;
            goto zig_block_11;
           } else {
            t91 = zig_false;
            goto zig_block_11;
           }
          }
          zig_block_11:;
          zig_bool t92;
          {
           if (t91) {
            zig_usize const t93 = t23;
            zig_u32 t94;
            memcpy(&t94, &t93, sizeof(zig_u32 ));
            t94 = zig_wrap_u32(t94, zig_as_u8(32));
            zig_bool const t95 = t94 < zig_as_u32(256);
            t92 = t95;
            goto zig_block_12;
           } else {
            t92 = zig_false;
            goto zig_block_12;
           }
          }
          zig_block_12:;
          zig_bool t96;
          {
           if (t92) {
            /* file:23:76 */
            zig_S_rand_Random__343 const t97 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
            zig_S_rand_Random__343 t98;
            t98 = t97;
            zig_S_rand_Random__343 const * const t99 = (zig_S_rand_Random__343 const * )&t98;
            zig_S_rand_Random__343 const t100 = (*t99);
            /* file:23:84 */
            zig_f32 const t101 = rand_Random_float__anon_695(t100);
            zig_bool const t102 = zig_le_f32(t101, (zig_f32 )zig_as_f32(0x1p-2, zig_as_i32(0x3e800000))) <= zig_as_i8(0);
            t96 = t102;
            goto zig_block_13;
           } else {
            t96 = zig_false;
            goto zig_block_13;
           }
          }
          zig_block_13:;
          if (t96) {
           /* file:24:17 */
           zig_i32 t103;
           zig_i32 t104[zig_as_u32(65536)];
           memcpy(t104, (zig_A_i32_65536 * )((zig_A_i32_65536 * )&generator_heightMap), sizeof(zig_i32 [zig_as_u32(65536)]));
           zig_usize const t105 = t20;
           zig_usize const t106 = t23;
           zig_T_tuple_7busize_2c_20u1_7d t107;
           t107.f1 = zig_mulo_u32(&t107.f0, t106, zig_as_u32(256), zig_as_u8(32));
           zig_u8 const t108 = t107.f1;
           zig_bool const t109 = t108 == zig_as_u8(0);
           {
            if (t109) {
             goto zig_block_14;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_740), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_14:;
           zig_usize const t110 = t107.f0;
           zig_T_tuple_7busize_2c_20u1_7d t111;
           t111.f1 = zig_addo_u32(&t111.f0, t105, t110, zig_as_u8(32));
           zig_u8 const t112 = t111.f1;
           zig_bool const t113 = t112 == zig_as_u8(0);
           {
            if (t113) {
             goto zig_block_15;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_741), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_15:;
           zig_usize const t114 = t111.f0;
           zig_usize const t115 = (zig_usize )t114;
           zig_bool const t116 = t115 < zig_as_u32(65536);
           {
            if (t116) {
             goto zig_block_16;
            } else {
             zig_breakpoint();
             zig_unreachable();
            }
           }
           zig_block_16:;
           zig_i32 const t117 = t104[t115];
           zig_T_tuple_7bi32_2c_20u1_7d t118;
           t118.f1 = zig_addo_i32(&t118.f0, t117, zig_as_i32(1), zig_as_u8(32));
           zig_u8 const t119 = t118.f1;
           zig_bool const t120 = t119 == zig_as_u8(0);
           {
            if (t120) {
             goto zig_block_17;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_742), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_17:;
           zig_i32 const t121 = t118.f0;
           zig_i32 * const t122 = (zig_i32 * )&t103;
           (*t122) = t121;
           /* var:ty */
           /* file:26:17 */
           zig_usize t123;
           /* file:26:45 */
           zig_S_rand_Random__343 const t124 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
           zig_S_rand_Random__343 t125;
           t125 = t124;
           zig_S_rand_Random__343 const * const t126 = (zig_S_rand_Random__343 const * )&t125;
           zig_S_rand_Random__343 const t127 = (*t126);
           /* file:26:51 */
           zig_usize const t128 = rand_Random_int__anon_712(t127);
           zig_usize const t129 = zig_mod_u32(t128, zig_as_u32(3));
           zig_T_tuple_7busize_2c_20u1_7d t130;
           t130.f1 = zig_addo_u32(&t130.f0, zig_as_u32(4), t129, zig_as_u8(32));
           zig_u8 const t131 = t130.f1;
           zig_bool const t132 = t131 == zig_as_u8(0);
           {
            if (t132) {
             goto zig_block_18;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_743), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_18:;
           zig_usize const t133 = t130.f0;
           zig_usize * const t134 = (zig_usize * )&t123;
           (*t134) = t133;
           /* var:th */
           /* file:28:17 */
           /* file:28:29 */
           zig_usize const t135 = t20;
           zig_u32 const t136 = (zig_u32 )t135;
           zig_i32 const t137 = t103;
           zig_bool const t138 = t137 >= zig_as_i32(0);
           {
            if (t138) {
             goto zig_block_19;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_744), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_19:;
           zig_u32 const t139 = (zig_u32 )t137;
           zig_usize const t140 = t23;
           zig_u32 const t141 = (zig_u32 )t140;
           zig_usize const t142 = t123;
           zig_u32 const t143 = (zig_u32 )t142;
           (zig_void )generator_growTree(t136, t139, t141, t143);
           goto zig_block_10;
          } else {
           goto zig_block_10;
          }
         }
         zig_block_10:;
         /* file:11:26 */
         zig_usize const t144 = t26;
         zig_T_tuple_7busize_2c_20u1_7d t145;
         t145.f1 = zig_addo_u32(&t145.f0, t144, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t146 = t145.f1;
         zig_bool const t147 = t146 == zig_as_u8(0);
         {
          if (t147) {
           goto zig_block_20;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_745), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_20:;
         zig_usize const t148 = t145.f0;
         t26 = t148;
         goto zig_block_3;
        } else {
         goto zig_block_2;
        }
       }
       zig_block_3:;
      }
     }
     zig_block_2:;
     /* file:6:22 */
     zig_usize const t149 = t16;
     zig_T_tuple_7busize_2c_20u1_7d t150;
     t150.f1 = zig_addo_u32(&t150.f0, t149, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t151 = t150.f1;
     zig_bool const t152 = t151 == zig_as_u8(0);
     {
      if (t152) {
       goto zig_block_21;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_create_tree__anon_746), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_21:;
     zig_usize const t153 = t150.f0;
     t16 = t153;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 return;
}

static zig_S_rand_SplitMix64__330 rand_SplitMix64_init(zig_u64 const a0) {
 /* file:2:9 */
 zig_S_rand_SplitMix64__330 t0;
 zig_S_rand_SplitMix64__330 * const t1 = (zig_S_rand_SplitMix64__330 * )&t0;
 zig_u64 * const t2 = (zig_u64 * )&t1->s;
 (*t2) = a0;
 /* file:2:9 */
 return t0;
}

static zig_u64 rand_SplitMix64_next(zig_S_rand_SplitMix64__330 * const a0) {
 /* file:2:9 */
 zig_S_rand_SplitMix64__330 * t0;
 t0 = a0;
 zig_S_rand_SplitMix64__330 * const * const t1 = (zig_S_rand_SplitMix64__330 * const * )&t0;
 zig_S_rand_SplitMix64__330 * const t2 = (*t1);
 zig_u64 * const t3 = (zig_u64 * )&t2->s;
 zig_u64 const t4 = (*t3);
 zig_u64 const t5 = zig_addw_u64(t4, zig_as_u64(11400714819323198485), zig_as_u8(64));
 (*t3) = t5;
 /* file:4:9 */
 zig_u64 t6;
 zig_u64 * const t7 = (zig_u64 * )&a0->s;
 zig_u64 const t8 = (*t7);
 zig_u64 * const t9 = (zig_u64 * )&t6;
 (*t9) = t8;
 /* var:z */
 /* file:5:9 */
 zig_u64 const t10 = t6;
 zig_u64 const t11 = t6;
 zig_u64 const t12 = zig_shr_u64(t11, zig_as_u8(30));
 zig_u64 const t13 = t10 ^ t12;
 zig_u64 const t14 = zig_mulw_u64(t13, zig_as_u64(13787848793156543929), zig_as_u8(64));
 t6 = t14;
 /* file:6:9 */
 zig_u64 const t15 = t6;
 zig_u64 const t16 = t6;
 zig_u64 const t17 = zig_shr_u64(t16, zig_as_u8(27));
 zig_u64 const t18 = t15 ^ t17;
 zig_u64 const t19 = zig_mulw_u64(t18, zig_as_u64(10723151780598845931), zig_as_u8(64));
 t6 = t19;
 /* file:7:9 */
 zig_u64 const t20 = t6;
 zig_u64 const t21 = t6;
 zig_u64 const t22 = zig_shr_u64(t21, zig_as_u8(31));
 zig_u64 const t23 = t20 ^ t22;
 /* file:7:9 */
 return t23;
}

zig_f64 grad(zig_usize const a0, zig_f64 const a1, zig_f64 const a2, zig_f64 const a3) {
 /* file:2:5 */
 zig_usize const t0 = a0 & zig_as_u32(15);
 /* file:2:13 */
 switch (t0) {
  case zig_as_u32(2): {
   /* file:5:20 */
   zig_f64 const t1 = zig_sub_f64(a1, a2);
   /* file:5:20 */
   return t1;
  }
  case zig_as_u32(3): {
   /* file:6:20 */
   zig_f64 const t2 = zig_neg_f64(a1);
   zig_f64 const t3 = zig_sub_f64(t2, a2);
   /* file:6:20 */
   return t3;
  }
  case zig_as_u32(4): {
   /* file:7:20 */
   zig_f64 const t4 = zig_add_f64(a1, a3);
   /* file:7:20 */
   return t4;
  }
  case zig_as_u32(5): {
   /* file:8:20 */
   zig_f64 const t5 = zig_sub_f64(a3, a1);
   /* file:8:20 */
   return t5;
  }
  case zig_as_u32(6): {
   /* file:9:20 */
   zig_f64 const t6 = zig_sub_f64(a1, a3);
   /* file:9:20 */
   return t6;
  }
  case zig_as_u32(7): {
   /* file:10:20 */
   zig_f64 const t7 = zig_neg_f64(a1);
   zig_f64 const t8 = zig_sub_f64(t7, a3);
   /* file:10:20 */
   return t8;
  }
  case zig_as_u32(8): {
   /* file:11:20 */
   zig_f64 const t9 = zig_add_f64(a2, a3);
   /* file:11:20 */
   return t9;
  }
  case zig_as_u32(10): {
   /* file:13:20 */
   zig_f64 const t10 = zig_sub_f64(a2, a3);
   /* file:13:20 */
   return t10;
  }
  case zig_as_u32(0): 
  case zig_as_u32(12): {
   /* file:3:20 */
   zig_f64 const t11 = zig_add_f64(a1, a2);
   /* file:3:20 */
   return t11;
  }
  case zig_as_u32(1): 
  case zig_as_u32(14): {
   /* file:4:20 */
   zig_f64 const t12 = zig_sub_f64(a2, a1);
   /* file:4:20 */
   return t12;
  }
  case zig_as_u32(9): 
  case zig_as_u32(13): {
   /* file:12:20 */
   zig_f64 const t13 = zig_sub_f64(a3, a2);
   /* file:12:20 */
   return t13;
  }
  default: {
   /* file:14:20 */
   zig_f64 const t14 = zig_neg_f64(a2);
   zig_f64 const t15 = zig_sub_f64(t14, a3);
   /* file:14:20 */
   return t15;
  }
 }
}

static zig_f64 perlin_pnoise(zig_f64 const a0, zig_f64 const a1, zig_u32 const a2) {
 /* file:2:5 */
 zig_f64 t0;
 /* file:2:17 */
 zig_f64 const t1 = __floatunsidf(a2);
 zig_f64 const t2 = perlin_noise(a0, a1, t1);
 t0 = t2;
 /* file:2:5 */
 return t0;
}

static zig_S_rand_Random__343 rand_Xoshiro256_random(zig_S_rand_Xoshiro256__255 * const a0) {
 /* file:2:5 */
 zig_S_rand_Random__343 t0;
 /* file:2:23 */
 zig_S_rand_Random__343 const t1 = rand_Random_init__anon_747(a0);
 t0 = t1;
 /* file:2:5 */
 return t0;
}

static zig_u32 rand_Random_int__anon_448(zig_S_rand_Random__343 const a0) {
 static zig_u8 const t1[zig_as_u32(4)] = {zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa)};
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:39 */
 /* file:4:9 */
 /* file:4:42 */
 /* file:6:9 */
 zig_u8 t0[zig_as_u32(4)];
 memset(&t0, zig_as_u8(0xaa), sizeof(zig_u8 [zig_as_u32(4)]));
 /* var:rand_bytes */
 /* file:7:9 */
 zig_S_rand_Random__343 t2;
 t2 = a0;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:7:16 */
 zig_A_u8_4 * const t5 = (zig_A_u8_4 * )(((uintptr_t)&t0) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_4 * const t6 = (zig_A_u8_4 * )t5;
 zig_L_u8 const t7 = { .ptr = &((*t6))[zig_as_u32(0)], .len = zig_as_u32(4) };
 rand_Random_bytes(t4, t7);
 /* file:12:9 */
 /* file:12:59 */
 zig_L_u8 const t8 = { .ptr = &(t0)[zig_as_u32(0)], .len = zig_as_u32(4) };
 zig_u32 const t9 = mem_readIntSliceNative__anon_1200(t8);
 /* var:byte_aligned_result */
 /* file:13:9 */
 zig_u32 const t10 = (zig_u32 )t9;
 /* var:unsigned_result */
 /* file:14:9 */
 zig_u32 t11;
 memcpy(&t11, &t10, sizeof(zig_u32 ));
 t11 = zig_wrap_u32(t11, zig_as_u8(32));
 /* file:14:9 */
 return t11;
}

static zig_f32 rand_Random_float__anon_695(zig_S_rand_Random__343 const a0) {
 /* file:5:9 */
 /* file:10:17 */
 zig_S_rand_Random__343 t0;
 t0 = a0;
 zig_S_rand_Random__343 const * const t1 = (zig_S_rand_Random__343 const * )&t0;
 zig_S_rand_Random__343 const t2 = (*t1);
 /* file:10:35 */
 zig_u64 const t3 = rand_Random_int__anon_1201(t2);
 /* var:rand */
 /* file:11:17 */
 zig_u8 t4;
 zig_u8 const t5 = zig_clz_u64(t3, zig_as_u8(64));
 zig_u8 * const t6 = (zig_u8 * )&t4;
 (*t6) = t5;
 /* var:rand_lz */
 /* file:12:21 */
 {
  zig_u8 const t7 = t4;
  zig_bool const t8 = t7 >= zig_as_u8(41);
  if (t8) {
   /* file:16:21 */
   zig_S_rand_Random__343 t9;
   t9 = a0;
   zig_S_rand_Random__343 const * const t10 = (zig_S_rand_Random__343 const * )&t9;
   zig_S_rand_Random__343 const t11 = (*t10);
   /* file:16:46 */
   zig_u64 const t12 = rand_Random_int__anon_1201(t11);
   zig_u8 const t13 = zig_clz_u64(t12, zig_as_u8(64));
   zig_T_tuple_7bu7_2c_20u1_7d t14;
   t14.f1 = zig_addo_u8(&t14.f0, zig_as_u8(41), t13, zig_as_u8(7));
   zig_u8 const t15 = t14.f1;
   zig_bool const t16 = t15 == zig_as_u8(0);
   {
    if (t16) {
     goto zig_block_1;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Random_float__anon_695__anon_1202), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_1:;
   zig_u8 const t17 = t14.f0;
   t4 = t17;
   /* file:17:25 */
   {
    zig_u8 const t18 = t4;
    zig_bool const t19 = t18 == zig_as_u8(105);
    if (t19) {
     /* file:19:25 */
     zig_u8 const t20 = t4;
     zig_S_rand_Random__343 t21;
     t21 = a0;
     zig_S_rand_Random__343 const * const t22 = (zig_S_rand_Random__343 const * )&t21;
     zig_S_rand_Random__343 const t23 = (*t22);
     /* file:19:46 */
     zig_u32 const t24 = rand_Random_int__anon_448(t23);
     zig_u32 const t25 = t24 | zig_as_u32(2047);
     zig_u8 const t26 = zig_clz_u32(t25, zig_as_u8(32));
     zig_u8 const t27 = (zig_u8 )t26;
     zig_T_tuple_7bu7_2c_20u1_7d t28;
     t28.f1 = zig_addo_u8(&t28.f0, t20, t27, zig_as_u8(7));
     zig_u8 const t29 = t28.f1;
     zig_bool const t30 = t29 == zig_as_u8(0);
     {
      if (t30) {
       goto zig_block_3;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Random_float__anon_695__anon_1203), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_3:;
     zig_u8 const t31 = t28.f0;
     t4 = t31;
     goto zig_block_2;
    } else {
     goto zig_block_2;
    }
   }
   zig_block_2:;
   goto zig_block_0;
  } else {
   goto zig_block_0;
  }
 }
 zig_block_0:;
 /* file:22:17 */
 zig_u32 const t32 = (zig_u32 )(t3 & zig_as_u32(0x7fffff));
 /* var:mantissa */
 /* file:23:17 */
 zig_u8 const t33 = t4;
 zig_T_tuple_7bu7_2c_20u1_7d t34;
 t34.f1 = zig_subo_u8(&t34.f0, zig_as_u8(126), t33, zig_as_u8(7));
 zig_u8 const t35 = t34.f1;
 zig_bool const t36 = t35 == zig_as_u8(0);
 {
  if (t36) {
   goto zig_block_4;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Random_float__anon_695__anon_1204), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_4:;
 zig_u8 const t37 = t34.f0;
 zig_u32 const t38 = (zig_u32 )t37;
 zig_u32 const t39 = zig_shlw_u32(t38, zig_as_u8(23), zig_as_u8(32));
 /* var:exponent */
 /* file:24:17 */
 zig_u32 const t40 = (zig_u32 )t32;
 zig_u32 const t41 = t39 | t40;
 zig_f32 t42;
 memcpy(&t42, &t41, sizeof(zig_f32 ));
 /* file:24:17 */
 return t42;
}

static zig_i32 rand_Random_int__anon_697(zig_S_rand_Random__343 const a0) {
 static zig_u8 const t1[zig_as_u32(4)] = {zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa)};
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:39 */
 /* file:4:9 */
 /* file:4:42 */
 /* file:6:9 */
 zig_u8 t0[zig_as_u32(4)];
 memset(&t0, zig_as_u8(0xaa), sizeof(zig_u8 [zig_as_u32(4)]));
 /* var:rand_bytes */
 /* file:7:9 */
 zig_S_rand_Random__343 t2;
 t2 = a0;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:7:16 */
 zig_A_u8_4 * const t5 = (zig_A_u8_4 * )(((uintptr_t)&t0) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_4 * const t6 = (zig_A_u8_4 * )t5;
 zig_L_u8 const t7 = { .ptr = &((*t6))[zig_as_u32(0)], .len = zig_as_u32(4) };
 rand_Random_bytes(t4, t7);
 /* file:12:9 */
 /* file:12:59 */
 zig_L_u8 const t8 = { .ptr = &(t0)[zig_as_u32(0)], .len = zig_as_u32(4) };
 zig_u32 const t9 = mem_readIntSliceNative__anon_1200(t8);
 /* var:byte_aligned_result */
 /* file:13:9 */
 zig_u32 const t10 = (zig_u32 )t9;
 /* var:unsigned_result */
 /* file:14:9 */
 zig_i32 t11;
 memcpy(&t11, &t10, sizeof(zig_i32 ));
 t11 = zig_wrap_i32(t11, zig_as_u8(32));
 /* file:14:9 */
 return t11;
}

static zig_void generator_fillOblateSpheroid(zig_i32 const a0, zig_i32 const a1, zig_i32 const a2, zig_f32 const a3, zig_u8 const a4) {
 /* file:2:5 */
 zig_isize t0;
 zig_isize const t1 = zig_wrap_i32(__fixsfsi(a3), zig_as_u8(32));
 zig_f32 const t2 = __floatsisf(t1);
 zig_f32 const t3 = zig_sub_f32(a3, t2);
 zig_bool const t4 = zig_lt_f32(t3, (zig_f32 )zig_as_f32(0x1p0, zig_as_i32(0x3f800000))) < zig_as_i8(0);
 zig_bool const t5 = zig_gt_f32(t3, (zig_f32 )zig_as_f32(-0x1p0, -zig_as_i32(0x40800000))) > zig_as_i8(0);
 zig_bool const t6 = t4 & t5;
 {
  if (t6) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1205), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_isize * const t7 = (zig_isize * )&t0;
 (*t7) = t1;
 /* var:r */
 /* file:3:5 */
 zig_isize t8;
 zig_isize const t9 = t0;
 zig_i32 t10;
 memcpy(&t10, &t9, sizeof(zig_i32 ));
 t10 = zig_wrap_i32(t10, zig_as_u8(32));
 zig_T_tuple_7bi32_2c_20u1_7d t11;
 t11.f1 = zig_subo_i32(&t11.f0, a2, t10, zig_as_u8(32));
 zig_u8 const t12 = t11.f1;
 zig_bool const t13 = t12 == zig_as_u8(0);
 {
  if (t13) {
   goto zig_block_1;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1206), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_1:;
 zig_i32 const t14 = t11.f0;
 zig_isize t15;
 memcpy(&t15, &t14, sizeof(zig_isize ));
 t15 = zig_wrap_i32(t15, zig_as_u8(32));
 t8 = t15;
 /* var:z */
 {
  while (zig_true) {
   {
    /* file:4:11 */
    zig_isize const t16 = t8;
    zig_isize const t17 = t0;
    zig_i32 t18;
    memcpy(&t18, &t17, sizeof(zig_i32 ));
    t18 = zig_wrap_i32(t18, zig_as_u8(32));
    zig_T_tuple_7bi32_2c_20u1_7d t19;
    t19.f1 = zig_addo_i32(&t19.f0, a2, t18, zig_as_u8(32));
    zig_u8 const t20 = t19.f1;
    zig_bool const t21 = t20 == zig_as_u8(0);
    {
     if (t21) {
      goto zig_block_4;
     } else {
      builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1207), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
     }
    }
    zig_block_4:;
    zig_i32 const t22 = t19.f0;
    zig_i32 t23;
    memcpy(&t23, &t16, sizeof(zig_i32 ));
    t23 = zig_wrap_i32(t23, zig_as_u8(32));
    zig_bool const t24 = t23 < t22;
    if (t24) {
     /* file:4:34 */
     /* file:5:5 */
     zig_isize t25;
     zig_isize const t26 = t0;
     zig_i32 t27;
     memcpy(&t27, &t26, sizeof(zig_i32 ));
     t27 = zig_wrap_i32(t27, zig_as_u8(32));
     zig_T_tuple_7bi32_2c_20u1_7d t28;
     t28.f1 = zig_subo_i32(&t28.f0, a1, t27, zig_as_u8(32));
     zig_u8 const t29 = t28.f1;
     zig_bool const t30 = t29 == zig_as_u8(0);
     {
      if (t30) {
       goto zig_block_5;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1208), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_5:;
     zig_i32 const t31 = t28.f0;
     zig_isize t32;
     memcpy(&t32, &t31, sizeof(zig_isize ));
     t32 = zig_wrap_i32(t32, zig_as_u8(32));
     t25 = t32;
     /* var:y */
     {
      while (zig_true) {
       {
        /* file:6:11 */
        zig_isize const t33 = t25;
        zig_isize const t34 = t0;
        zig_i32 t35;
        memcpy(&t35, &t34, sizeof(zig_i32 ));
        t35 = zig_wrap_i32(t35, zig_as_u8(32));
        zig_T_tuple_7bi32_2c_20u1_7d t36;
        t36.f1 = zig_addo_i32(&t36.f0, a1, t35, zig_as_u8(32));
        zig_u8 const t37 = t36.f1;
        zig_bool const t38 = t37 == zig_as_u8(0);
        {
         if (t38) {
          goto zig_block_8;
         } else {
          builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1209), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
         }
        }
        zig_block_8:;
        zig_i32 const t39 = t36.f0;
        zig_i32 t40;
        memcpy(&t40, &t33, sizeof(zig_i32 ));
        t40 = zig_wrap_i32(t40, zig_as_u8(32));
        zig_bool const t41 = t40 < t39;
        if (t41) {
         /* file:6:34 */
         /* file:7:5 */
         zig_isize t42;
         zig_isize const t43 = t0;
         zig_i32 t44;
         memcpy(&t44, &t43, sizeof(zig_i32 ));
         t44 = zig_wrap_i32(t44, zig_as_u8(32));
         zig_T_tuple_7bi32_2c_20u1_7d t45;
         t45.f1 = zig_subo_i32(&t45.f0, a0, t44, zig_as_u8(32));
         zig_u8 const t46 = t45.f1;
         zig_bool const t47 = t46 == zig_as_u8(0);
         {
          if (t47) {
           goto zig_block_9;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1210), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_9:;
         zig_i32 const t48 = t45.f0;
         zig_isize t49;
         memcpy(&t49, &t48, sizeof(zig_isize ));
         t49 = zig_wrap_i32(t49, zig_as_u8(32));
         t42 = t49;
         /* var:x */
         {
          while (zig_true) {
           {
            /* file:8:11 */
            zig_isize const t50 = t42;
            zig_isize const t51 = t0;
            zig_i32 t52;
            memcpy(&t52, &t51, sizeof(zig_i32 ));
            t52 = zig_wrap_i32(t52, zig_as_u8(32));
            zig_T_tuple_7bi32_2c_20u1_7d t53;
            t53.f1 = zig_addo_i32(&t53.f0, a0, t52, zig_as_u8(32));
            zig_u8 const t54 = t53.f1;
            zig_bool const t55 = t54 == zig_as_u8(0);
            {
             if (t55) {
              goto zig_block_12;
             } else {
              builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1211), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
             }
            }
            zig_block_12:;
            zig_i32 const t56 = t53.f0;
            zig_i32 t57;
            memcpy(&t57, &t50, sizeof(zig_i32 ));
            t57 = zig_wrap_i32(t57, zig_as_u8(32));
            zig_bool const t58 = t57 < t56;
            if (t58) {
             /* file:8:34 */
             /* file:10:9 */
             zig_isize t59;
             zig_isize const t60 = t42;
             zig_isize t61;
             memcpy(&t61, &a0, sizeof(zig_isize ));
             t61 = zig_wrap_i32(t61, zig_as_u8(32));
             zig_T_tuple_7bisize_2c_20u1_7d t62;
             t62.f1 = zig_subo_i32(&t62.f0, t60, t61, zig_as_u8(32));
             zig_u8 const t63 = t62.f1;
             zig_bool const t64 = t63 == zig_as_u8(0);
             {
              if (t64) {
               goto zig_block_13;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1212), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_13:;
             zig_isize const t65 = t62.f0;
             zig_isize * const t66 = (zig_isize * )&t59;
             (*t66) = t65;
             /* var:dx */
             /* file:11:9 */
             zig_isize t67;
             zig_isize const t68 = t25;
             zig_isize t69;
             memcpy(&t69, &a1, sizeof(zig_isize ));
             t69 = zig_wrap_i32(t69, zig_as_u8(32));
             zig_T_tuple_7bisize_2c_20u1_7d t70;
             t70.f1 = zig_subo_i32(&t70.f0, t68, t69, zig_as_u8(32));
             zig_u8 const t71 = t70.f1;
             zig_bool const t72 = t71 == zig_as_u8(0);
             {
              if (t72) {
               goto zig_block_14;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1213), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_14:;
             zig_isize const t73 = t70.f0;
             zig_isize * const t74 = (zig_isize * )&t67;
             (*t74) = t73;
             /* var:dy */
             /* file:12:9 */
             zig_isize t75;
             zig_isize const t76 = t8;
             zig_isize t77;
             memcpy(&t77, &a2, sizeof(zig_isize ));
             t77 = zig_wrap_i32(t77, zig_as_u8(32));
             zig_T_tuple_7bisize_2c_20u1_7d t78;
             t78.f1 = zig_subo_i32(&t78.f0, t76, t77, zig_as_u8(32));
             zig_u8 const t79 = t78.f1;
             zig_bool const t80 = t79 == zig_as_u8(0);
             {
              if (t80) {
               goto zig_block_15;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1214), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_15:;
             zig_isize const t81 = t78.f0;
             zig_isize * const t82 = (zig_isize * )&t75;
             (*t82) = t81;
             /* var:dz */
             /* file:14:12 */
             {
              zig_isize const t83 = t59;
              zig_isize const t84 = t59;
              zig_T_tuple_7bisize_2c_20u1_7d t85;
              t85.f1 = zig_mulo_i32(&t85.f0, t83, t84, zig_as_u8(32));
              zig_u8 const t86 = t85.f1;
              zig_bool const t87 = t86 == zig_as_u8(0);
              {
               if (t87) {
                goto zig_block_17;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1215), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_17:;
              zig_isize const t88 = t85.f0;
              zig_isize const t89 = t67;
              zig_T_tuple_7bisize_2c_20u1_7d t90;
              t90.f1 = zig_mulo_i32(&t90.f0, zig_as_i32(2), t89, zig_as_u8(32));
              zig_u8 const t91 = t90.f1;
              zig_bool const t92 = t91 == zig_as_u8(0);
              {
               if (t92) {
                goto zig_block_18;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1216), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_18:;
              zig_isize const t93 = t90.f0;
              zig_isize const t94 = t67;
              zig_T_tuple_7bisize_2c_20u1_7d t95;
              t95.f1 = zig_mulo_i32(&t95.f0, t93, t94, zig_as_u8(32));
              zig_u8 const t96 = t95.f1;
              zig_bool const t97 = t96 == zig_as_u8(0);
              {
               if (t97) {
                goto zig_block_19;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1217), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_19:;
              zig_isize const t98 = t95.f0;
              zig_T_tuple_7bisize_2c_20u1_7d t99;
              t99.f1 = zig_addo_i32(&t99.f0, t88, t98, zig_as_u8(32));
              zig_u8 const t100 = t99.f1;
              zig_bool const t101 = t100 == zig_as_u8(0);
              {
               if (t101) {
                goto zig_block_20;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1218), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_20:;
              zig_isize const t102 = t99.f0;
              zig_isize const t103 = t75;
              zig_isize const t104 = t75;
              zig_T_tuple_7bisize_2c_20u1_7d t105;
              t105.f1 = zig_mulo_i32(&t105.f0, t103, t104, zig_as_u8(32));
              zig_u8 const t106 = t105.f1;
              zig_bool const t107 = t106 == zig_as_u8(0);
              {
               if (t107) {
                goto zig_block_21;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1219), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_21:;
              zig_isize const t108 = t105.f0;
              zig_T_tuple_7bisize_2c_20u1_7d t109;
              t109.f1 = zig_addo_i32(&t109.f0, t102, t108, zig_as_u8(32));
              zig_u8 const t110 = t109.f1;
              zig_bool const t111 = t110 == zig_as_u8(0);
              {
               if (t111) {
                goto zig_block_22;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1220), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_22:;
              zig_isize const t112 = t109.f0;
              zig_isize const t113 = t0;
              zig_isize const t114 = t0;
              zig_T_tuple_7bisize_2c_20u1_7d t115;
              t115.f1 = zig_mulo_i32(&t115.f0, t113, t114, zig_as_u8(32));
              zig_u8 const t116 = t115.f1;
              zig_bool const t117 = t116 == zig_as_u8(0);
              {
               if (t117) {
                goto zig_block_23;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1221), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_23:;
              zig_isize const t118 = t115.f0;
              zig_i32 t119;
              memcpy(&t119, &t112, sizeof(zig_i32 ));
              t119 = zig_wrap_i32(t119, zig_as_u8(32));
              zig_i32 t120;
              memcpy(&t120, &t118, sizeof(zig_i32 ));
              t120 = zig_wrap_i32(t120, zig_as_u8(32));
              zig_bool const t121 = t119 < t120;
              if (t121) {
               /* file:15:16 */
               {
                zig_isize const t122 = t42;
                zig_i32 t123;
                memcpy(&t123, &t122, sizeof(zig_i32 ));
                t123 = zig_wrap_i32(t123, zig_as_u8(32));
                zig_bool const t124 = t123 >= zig_as_i32(0);
                zig_bool t125;
                {
                 if (t124) {
                  zig_isize const t126 = t42;
                  zig_i32 t127;
                  memcpy(&t127, &t126, sizeof(zig_i32 ));
                  t127 = zig_wrap_i32(t127, zig_as_u8(32));
                  zig_bool const t128 = t127 < zig_as_i32(256);
                  t125 = t128;
                  goto zig_block_25;
                 } else {
                  t125 = zig_false;
                  goto zig_block_25;
                 }
                }
                zig_block_25:;
                zig_bool t129;
                {
                 if (t125) {
                  zig_isize const t130 = t25;
                  zig_i32 t131;
                  memcpy(&t131, &t130, sizeof(zig_i32 ));
                  t131 = zig_wrap_i32(t131, zig_as_u8(32));
                  zig_bool const t132 = t131 >= zig_as_i32(0);
                  t129 = t132;
                  goto zig_block_26;
                 } else {
                  t129 = zig_false;
                  goto zig_block_26;
                 }
                }
                zig_block_26:;
                zig_bool t133;
                {
                 if (t129) {
                  zig_isize const t134 = t25;
                  zig_i32 t135;
                  memcpy(&t135, &t134, sizeof(zig_i32 ));
                  t135 = zig_wrap_i32(t135, zig_as_u8(32));
                  zig_bool const t136 = t135 < zig_as_i32(64);
                  t133 = t136;
                  goto zig_block_27;
                 } else {
                  t133 = zig_false;
                  goto zig_block_27;
                 }
                }
                zig_block_27:;
                zig_bool t137;
                {
                 if (t133) {
                  zig_isize const t138 = t8;
                  zig_i32 t139;
                  memcpy(&t139, &t138, sizeof(zig_i32 ));
                  t139 = zig_wrap_i32(t139, zig_as_u8(32));
                  zig_bool const t140 = t139 >= zig_as_i32(0);
                  t137 = t140;
                  goto zig_block_28;
                 } else {
                  t137 = zig_false;
                  goto zig_block_28;
                 }
                }
                zig_block_28:;
                zig_bool t141;
                {
                 if (t137) {
                  zig_isize const t142 = t8;
                  zig_i32 t143;
                  memcpy(&t143, &t142, sizeof(zig_i32 ));
                  t143 = zig_wrap_i32(t143, zig_as_u8(32));
                  zig_bool const t144 = t143 < zig_as_i32(256);
                  t141 = t144;
                  goto zig_block_29;
                 } else {
                  t141 = zig_false;
                  goto zig_block_29;
                 }
                }
                zig_block_29:;
                if (t141) {
                 /* file:16:17 */
                 zig_usize t145;
                 /* file:16:33 */
                 zig_isize const t146 = t42;
                 zig_bool const t147 = t146 >= zig_as_i32(0);
                 {
                  if (t147) {
                   goto zig_block_30;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1222), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_30:;
                 zig_u32 const t148 = (zig_u32 )t146;
                 zig_isize const t149 = t25;
                 zig_bool const t150 = t149 >= zig_as_i32(0);
                 {
                  if (t150) {
                   goto zig_block_31;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1223), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_31:;
                 zig_u32 const t151 = (zig_u32 )t149;
                 zig_isize const t152 = t8;
                 zig_bool const t153 = t152 >= zig_as_i32(0);
                 {
                  if (t153) {
                   goto zig_block_32;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1224), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_32:;
                 zig_u32 const t154 = (zig_u32 )t152;
                 zig_usize const t155 = generator_getIdx(t148, t151, t154);
                 zig_usize * const t156 = (zig_usize * )&t145;
                 (*t156) = t155;
                 /* var:idx */
                 /* file:17:17 */
                 zig_u8 t157;
                 zig_u8 * const t158 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                 zig_usize const t159 = t145;
                 zig_u8 const t160 = t158[t159];
                 zig_u8 * const t161 = (zig_u8 * )&t157;
                 (*t161) = t160;
                 /* var:blk */
                 /* file:19:20 */
                 {
                  zig_u8 const t162 = t157;
                  zig_bool const t163 = t162 == zig_as_u8(1);
                  if (t163) {
                   /* file:20:21 */
                   zig_usize const t164 = t145;
                   zig_u8 * const t165 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                   zig_u8 * const t166 = &(t165)[t164];
                   (*t166) = a4;
                   goto zig_block_33;
                  } else {
                   goto zig_block_33;
                  }
                 }
                 zig_block_33:;
                 goto zig_block_24;
                } else {
                 goto zig_block_24;
                }
               }
               zig_block_24:;
               goto zig_block_16;
              } else {
               goto zig_block_16;
              }
             }
             zig_block_16:;
             /* file:8:26 */
             zig_isize const t167 = t42;
             zig_T_tuple_7bisize_2c_20u1_7d t168;
             t168.f1 = zig_addo_i32(&t168.f0, t167, zig_as_i32(1), zig_as_u8(32));
             zig_u8 const t169 = t168.f1;
             zig_bool const t170 = t169 == zig_as_u8(0);
             {
              if (t170) {
               goto zig_block_34;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1225), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_34:;
             zig_isize const t171 = t168.f0;
             t42 = t171;
             goto zig_block_11;
            } else {
             goto zig_block_10;
            }
           }
           zig_block_11:;
          }
         }
         zig_block_10:;
         /* file:6:26 */
         zig_isize const t172 = t25;
         zig_T_tuple_7bisize_2c_20u1_7d t173;
         t173.f1 = zig_addo_i32(&t173.f0, t172, zig_as_i32(1), zig_as_u8(32));
         zig_u8 const t174 = t173.f1;
         zig_bool const t175 = t174 == zig_as_u8(0);
         {
          if (t175) {
           goto zig_block_35;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1226), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_35:;
         zig_isize const t176 = t173.f0;
         t25 = t176;
         goto zig_block_7;
        } else {
         goto zig_block_6;
        }
       }
       zig_block_7:;
      }
     }
     zig_block_6:;
     /* file:4:26 */
     zig_isize const t177 = t8;
     zig_T_tuple_7bisize_2c_20u1_7d t178;
     t178.f1 = zig_addo_i32(&t178.f0, t177, zig_as_i32(1), zig_as_u8(32));
     zig_u8 const t179 = t178.f1;
     zig_bool const t180 = t179 == zig_as_u8(0);
     {
      if (t180) {
       goto zig_block_36;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_fillOblateSpheroid__anon_1227), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_36:;
     zig_isize const t181 = t178.f0;
     t8 = t181;
     goto zig_block_3;
    } else {
     goto zig_block_2;
    }
   }
   zig_block_3:;
  }
 }
 zig_block_2:;
 return;
}

static zig_u8 rand_Random_int__anon_710(zig_S_rand_Random__343 const a0) {
 static zig_u8 const t1[zig_as_u32(1)] = {zig_as_u8(0xaa)};
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:39 */
 /* file:4:9 */
 /* file:4:42 */
 /* file:6:9 */
 zig_u8 t0[zig_as_u32(1)];
 memset(&t0, zig_as_u8(0xaa), sizeof(zig_u8 [zig_as_u32(1)]));
 /* var:rand_bytes */
 /* file:7:9 */
 zig_S_rand_Random__343 t2;
 t2 = a0;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:7:16 */
 zig_A_u8_1 * const t5 = (zig_A_u8_1 * )(((uintptr_t)&t0) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_1 * const t6 = (zig_A_u8_1 * )t5;
 zig_L_u8 const t7 = { .ptr = &((*t6))[zig_as_u32(0)], .len = zig_as_u32(1) };
 rand_Random_bytes(t4, t7);
 /* file:12:9 */
 /* file:12:59 */
 zig_L_u8 const t8 = { .ptr = &(t0)[zig_as_u32(0)], .len = zig_as_u32(1) };
 zig_u8 const t9 = mem_readIntSliceNative__anon_1228(t8);
 /* var:byte_aligned_result */
 /* file:13:9 */
 zig_u8 const t10 = (zig_u8 )t9;
 /* var:unsigned_result */
 /* file:14:9 */
 zig_u8 t11;
 memcpy(&t11, &t10, sizeof(zig_u8 ));
 t11 = zig_wrap_u8(t11, zig_as_u8(8));
 /* file:14:9 */
 return t11;
}

static zig_usize rand_Random_int__anon_712(zig_S_rand_Random__343 const a0) {
 static zig_u8 const t1[zig_as_u32(4)] = {zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa)};
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:39 */
 /* file:4:9 */
 /* file:4:42 */
 /* file:6:9 */
 zig_u8 t0[zig_as_u32(4)];
 memset(&t0, zig_as_u8(0xaa), sizeof(zig_u8 [zig_as_u32(4)]));
 /* var:rand_bytes */
 /* file:7:9 */
 zig_S_rand_Random__343 t2;
 t2 = a0;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:7:16 */
 zig_A_u8_4 * const t5 = (zig_A_u8_4 * )(((uintptr_t)&t0) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_4 * const t6 = (zig_A_u8_4 * )t5;
 zig_L_u8 const t7 = { .ptr = &((*t6))[zig_as_u32(0)], .len = zig_as_u32(4) };
 rand_Random_bytes(t4, t7);
 /* file:12:9 */
 /* file:12:59 */
 zig_L_u8 const t8 = { .ptr = &(t0)[zig_as_u32(0)], .len = zig_as_u32(4) };
 zig_u32 const t9 = mem_readIntSliceNative__anon_1200(t8);
 /* var:byte_aligned_result */
 /* file:13:9 */
 zig_u32 const t10 = (zig_u32 )t9;
 /* var:unsigned_result */
 /* file:14:9 */
 zig_usize t11;
 memcpy(&t11, &t10, sizeof(zig_usize ));
 t11 = zig_wrap_u32(t11, zig_as_u8(32));
 /* file:14:9 */
 return t11;
}

static zig_bool generator_growTree(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2, zig_u32 const a3) {
 /* file:2:8 */
 {
  zig_bool const t0 = a0 > zig_as_u32(2);
  zig_bool t1;
  {
   if (t0) {
    zig_bool const t2 = a2 > zig_as_u32(2);
    t1 = t2;
    goto zig_block_1;
   } else {
    t1 = zig_false;
    goto zig_block_1;
   }
  }
  zig_block_1:;
  zig_bool t3;
  {
   if (t1) {
    zig_bool const t4 = a1 > zig_as_u32(0);
    t3 = t4;
    goto zig_block_2;
   } else {
    t3 = zig_false;
    goto zig_block_2;
   }
  }
  zig_block_2:;
  zig_bool t5;
  {
   if (t3) {
    zig_bool const t6 = a1 < zig_as_u32(50);
    t5 = t6;
    goto zig_block_3;
   } else {
    t5 = zig_false;
    goto zig_block_3;
   }
  }
  zig_block_3:;
  zig_bool t7;
  {
   if (t5) {
    zig_bool const t8 = a0 < zig_as_u32(254);
    t7 = t8;
    goto zig_block_4;
   } else {
    t7 = zig_false;
    goto zig_block_4;
   }
  }
  zig_block_4:;
  zig_bool t9;
  {
   if (t7) {
    zig_bool const t10 = a2 < zig_as_u32(254);
    t9 = t10;
    goto zig_block_5;
   } else {
    t9 = zig_false;
    goto zig_block_5;
   }
  }
  zig_block_5:;
  if (t9) {
   /* file:3:8 */
   {
    /* file:3:22 */
    zig_bool const t11 = generator_isSpaceForTree(a0, a1, a2);
    if (t11) {
     /* file:4:5 */
     zig_T_tuple_7bu32_2c_20u1_7d t12;
     t12.f1 = zig_addo_u32(&t12.f0, a1, a3, zig_as_u8(32));
     zig_u8 const t13 = t12.f1;
     zig_bool const t14 = t13 == zig_as_u8(0);
     {
      if (t14) {
       goto zig_block_7;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1229), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_7:;
     zig_u32 const t15 = t12.f0;
     /* var:max */
     /* file:6:5 */
     zig_u32 t16;
     t16 = t15;
     /* var:m */
     {
      while (zig_true) {
       {
        /* file:7:11 */
        zig_u32 const t17 = t16;
        zig_bool const t18 = t17 >= a1;
        if (t18) {
         /* file:7:30 */
         /* file:8:12 */
         {
          zig_u32 const t19 = t16;
          zig_bool const t20 = t19 == t15;
          if (t20) {
           /* file:9:13 */
           /* file:9:29 */
           zig_T_tuple_7bu32_2c_20u1_7d t21;
           t21.f1 = zig_subo_u32(&t21.f0, a0, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t22 = t21.f1;
           zig_bool const t23 = t22 == zig_as_u8(0);
           {
            if (t23) {
             goto zig_block_11;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1230), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_11:;
           zig_u32 const t24 = t21.f0;
           zig_u32 const t25 = t16;
           zig_usize const t26 = generator_getIdx(t24, t25, a2);
           zig_u8 * const t27 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t28 = &(t27)[t26];
           (*t28) = zig_as_u8(18);
           /* file:10:13 */
           /* file:10:29 */
           zig_T_tuple_7bu32_2c_20u1_7d t29;
           t29.f1 = zig_addo_u32(&t29.f0, a0, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t30 = t29.f1;
           zig_bool const t31 = t30 == zig_as_u8(0);
           {
            if (t31) {
             goto zig_block_12;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1231), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_12:;
           zig_u32 const t32 = t29.f0;
           zig_u32 const t33 = t16;
           zig_usize const t34 = generator_getIdx(t32, t33, a2);
           zig_u8 * const t35 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t36 = &(t35)[t34];
           (*t36) = zig_as_u8(18);
           /* file:11:13 */
           /* file:11:29 */
           zig_u32 const t37 = t16;
           zig_T_tuple_7bu32_2c_20u1_7d t38;
           t38.f1 = zig_subo_u32(&t38.f0, a2, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t39 = t38.f1;
           zig_bool const t40 = t39 == zig_as_u8(0);
           {
            if (t40) {
             goto zig_block_13;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1232), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_13:;
           zig_u32 const t41 = t38.f0;
           zig_usize const t42 = generator_getIdx(a0, t37, t41);
           zig_u8 * const t43 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t44 = &(t43)[t42];
           (*t44) = zig_as_u8(18);
           /* file:12:13 */
           /* file:12:29 */
           zig_u32 const t45 = t16;
           zig_T_tuple_7bu32_2c_20u1_7d t46;
           t46.f1 = zig_addo_u32(&t46.f0, a2, zig_as_u32(1), zig_as_u8(32));
           zig_u8 const t47 = t46.f1;
           zig_bool const t48 = t47 == zig_as_u8(0);
           {
            if (t48) {
             goto zig_block_14;
            } else {
             builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1233), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
            }
           }
           zig_block_14:;
           zig_u32 const t49 = t46.f0;
           zig_usize const t50 = generator_getIdx(a0, t45, t49);
           zig_u8 * const t51 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t52 = &(t51)[t50];
           (*t52) = zig_as_u8(18);
           /* file:13:13 */
           /* file:13:29 */
           zig_u32 const t53 = t16;
           zig_usize const t54 = generator_getIdx(a0, t53, a2);
           zig_u8 * const t55 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
           zig_u8 * const t56 = &(t55)[t54];
           (*t56) = zig_as_u8(18);
           goto zig_block_10;
          } else {
           {
            /* file:14:19 */
            zig_u32 const t57 = t16;
            zig_T_tuple_7bu32_2c_20u1_7d t58;
            t58.f1 = zig_subo_u32(&t58.f0, t15, zig_as_u32(1), zig_as_u8(32));
            zig_u8 const t59 = t58.f1;
            zig_bool const t60 = t59 == zig_as_u8(0);
            {
             if (t60) {
              goto zig_block_16;
             } else {
              builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1234), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
             }
            }
            zig_block_16:;
            zig_u32 const t61 = t58.f0;
            zig_bool const t62 = t57 == t61;
            if (t62) {
             /* file:15:13 */
             /* file:15:29 */
             zig_T_tuple_7bu32_2c_20u1_7d t63;
             t63.f1 = zig_subo_u32(&t63.f0, a0, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t64 = t63.f1;
             zig_bool const t65 = t64 == zig_as_u8(0);
             {
              if (t65) {
               goto zig_block_17;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1235), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_17:;
             zig_u32 const t66 = t63.f0;
             zig_u32 const t67 = t16;
             zig_usize const t68 = generator_getIdx(t66, t67, a2);
             zig_u8 * const t69 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t70 = &(t69)[t68];
             (*t70) = zig_as_u8(18);
             /* file:16:13 */
             /* file:16:29 */
             zig_T_tuple_7bu32_2c_20u1_7d t71;
             t71.f1 = zig_addo_u32(&t71.f0, a0, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t72 = t71.f1;
             zig_bool const t73 = t72 == zig_as_u8(0);
             {
              if (t73) {
               goto zig_block_18;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1236), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_18:;
             zig_u32 const t74 = t71.f0;
             zig_u32 const t75 = t16;
             zig_usize const t76 = generator_getIdx(t74, t75, a2);
             zig_u8 * const t77 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t78 = &(t77)[t76];
             (*t78) = zig_as_u8(18);
             /* file:17:13 */
             /* file:17:29 */
             zig_u32 const t79 = t16;
             zig_T_tuple_7bu32_2c_20u1_7d t80;
             t80.f1 = zig_subo_u32(&t80.f0, a2, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t81 = t80.f1;
             zig_bool const t82 = t81 == zig_as_u8(0);
             {
              if (t82) {
               goto zig_block_19;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1237), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_19:;
             zig_u32 const t83 = t80.f0;
             zig_usize const t84 = generator_getIdx(a0, t79, t83);
             zig_u8 * const t85 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t86 = &(t85)[t84];
             (*t86) = zig_as_u8(18);
             /* file:18:13 */
             /* file:18:29 */
             zig_u32 const t87 = t16;
             zig_T_tuple_7bu32_2c_20u1_7d t88;
             t88.f1 = zig_addo_u32(&t88.f0, a2, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t89 = t88.f1;
             zig_bool const t90 = t89 == zig_as_u8(0);
             {
              if (t90) {
               goto zig_block_20;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1238), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_20:;
             zig_u32 const t91 = t88.f0;
             zig_usize const t92 = generator_getIdx(a0, t87, t91);
             zig_u8 * const t93 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t94 = &(t93)[t92];
             (*t94) = zig_as_u8(18);
             /* file:20:16 */
             {
              /* file:20:31 */
              zig_S_rand_Random__343 const t95 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
              zig_S_rand_Random__343 t96;
              t96 = t95;
              zig_S_rand_Random__343 const * const t97 = (zig_S_rand_Random__343 const * )&t96;
              zig_S_rand_Random__343 const t98 = (*t97);
              /* file:20:37 */
              zig_usize const t99 = rand_Random_int__anon_712(t98);
              zig_usize const t100 = zig_mod_u32(t99, zig_as_u32(2));
              zig_u32 t101;
              memcpy(&t101, &t100, sizeof(zig_u32 ));
              t101 = zig_wrap_u32(t101, zig_as_u8(32));
              zig_bool const t102 = t101 == zig_as_u32(0);
              if (t102) {
               /* file:21:17 */
               /* file:21:33 */
               zig_T_tuple_7bu32_2c_20u1_7d t103;
               t103.f1 = zig_subo_u32(&t103.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t104 = t103.f1;
               zig_bool const t105 = t104 == zig_as_u8(0);
               {
                if (t105) {
                 goto zig_block_22;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1239), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_22:;
               zig_u32 const t106 = t103.f0;
               zig_u32 const t107 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t108;
               t108.f1 = zig_subo_u32(&t108.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t109 = t108.f1;
               zig_bool const t110 = t109 == zig_as_u8(0);
               {
                if (t110) {
                 goto zig_block_23;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1240), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_23:;
               zig_u32 const t111 = t108.f0;
               zig_usize const t112 = generator_getIdx(t106, t107, t111);
               zig_u8 * const t113 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t114 = &(t113)[t112];
               (*t114) = zig_as_u8(18);
               goto zig_block_21;
              } else {
               goto zig_block_21;
              }
             }
             zig_block_21:;
             /* file:23:16 */
             {
              /* file:23:31 */
              zig_S_rand_Random__343 const t115 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
              zig_S_rand_Random__343 t116;
              t116 = t115;
              zig_S_rand_Random__343 const * const t117 = (zig_S_rand_Random__343 const * )&t116;
              zig_S_rand_Random__343 const t118 = (*t117);
              /* file:23:37 */
              zig_usize const t119 = rand_Random_int__anon_712(t118);
              zig_usize const t120 = zig_mod_u32(t119, zig_as_u32(2));
              zig_u32 t121;
              memcpy(&t121, &t120, sizeof(zig_u32 ));
              t121 = zig_wrap_u32(t121, zig_as_u8(32));
              zig_bool const t122 = t121 == zig_as_u32(0);
              if (t122) {
               /* file:24:17 */
               /* file:24:33 */
               zig_T_tuple_7bu32_2c_20u1_7d t123;
               t123.f1 = zig_addo_u32(&t123.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t124 = t123.f1;
               zig_bool const t125 = t124 == zig_as_u8(0);
               {
                if (t125) {
                 goto zig_block_25;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1241), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_25:;
               zig_u32 const t126 = t123.f0;
               zig_u32 const t127 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t128;
               t128.f1 = zig_subo_u32(&t128.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t129 = t128.f1;
               zig_bool const t130 = t129 == zig_as_u8(0);
               {
                if (t130) {
                 goto zig_block_26;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1242), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_26:;
               zig_u32 const t131 = t128.f0;
               zig_usize const t132 = generator_getIdx(t126, t127, t131);
               zig_u8 * const t133 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t134 = &(t133)[t132];
               (*t134) = zig_as_u8(18);
               goto zig_block_24;
              } else {
               goto zig_block_24;
              }
             }
             zig_block_24:;
             /* file:26:16 */
             {
              /* file:26:31 */
              zig_S_rand_Random__343 const t135 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
              zig_S_rand_Random__343 t136;
              t136 = t135;
              zig_S_rand_Random__343 const * const t137 = (zig_S_rand_Random__343 const * )&t136;
              zig_S_rand_Random__343 const t138 = (*t137);
              /* file:26:37 */
              zig_usize const t139 = rand_Random_int__anon_712(t138);
              zig_usize const t140 = zig_mod_u32(t139, zig_as_u32(2));
              zig_u32 t141;
              memcpy(&t141, &t140, sizeof(zig_u32 ));
              t141 = zig_wrap_u32(t141, zig_as_u8(32));
              zig_bool const t142 = t141 == zig_as_u32(0);
              if (t142) {
               /* file:27:17 */
               /* file:27:33 */
               zig_T_tuple_7bu32_2c_20u1_7d t143;
               t143.f1 = zig_subo_u32(&t143.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t144 = t143.f1;
               zig_bool const t145 = t144 == zig_as_u8(0);
               {
                if (t145) {
                 goto zig_block_28;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1243), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_28:;
               zig_u32 const t146 = t143.f0;
               zig_u32 const t147 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t148;
               t148.f1 = zig_addo_u32(&t148.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t149 = t148.f1;
               zig_bool const t150 = t149 == zig_as_u8(0);
               {
                if (t150) {
                 goto zig_block_29;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1244), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_29:;
               zig_u32 const t151 = t148.f0;
               zig_usize const t152 = generator_getIdx(t146, t147, t151);
               zig_u8 * const t153 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t154 = &(t153)[t152];
               (*t154) = zig_as_u8(18);
               goto zig_block_27;
              } else {
               goto zig_block_27;
              }
             }
             zig_block_27:;
             /* file:29:16 */
             {
              /* file:29:31 */
              zig_S_rand_Random__343 const t155 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
              zig_S_rand_Random__343 t156;
              t156 = t155;
              zig_S_rand_Random__343 const * const t157 = (zig_S_rand_Random__343 const * )&t156;
              zig_S_rand_Random__343 const t158 = (*t157);
              /* file:29:37 */
              zig_usize const t159 = rand_Random_int__anon_712(t158);
              zig_usize const t160 = zig_mod_u32(t159, zig_as_u32(2));
              zig_u32 t161;
              memcpy(&t161, &t160, sizeof(zig_u32 ));
              t161 = zig_wrap_u32(t161, zig_as_u8(32));
              zig_bool const t162 = t161 == zig_as_u32(0);
              if (t162) {
               /* file:30:17 */
               /* file:30:33 */
               zig_T_tuple_7bu32_2c_20u1_7d t163;
               t163.f1 = zig_addo_u32(&t163.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t164 = t163.f1;
               zig_bool const t165 = t164 == zig_as_u8(0);
               {
                if (t165) {
                 goto zig_block_31;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1245), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_31:;
               zig_u32 const t166 = t163.f0;
               zig_u32 const t167 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t168;
               t168.f1 = zig_addo_u32(&t168.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t169 = t168.f1;
               zig_bool const t170 = t169 == zig_as_u8(0);
               {
                if (t170) {
                 goto zig_block_32;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1246), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_32:;
               zig_u32 const t171 = t168.f0;
               zig_usize const t172 = generator_getIdx(t166, t167, t171);
               zig_u8 * const t173 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t174 = &(t173)[t172];
               (*t174) = zig_as_u8(18);
               goto zig_block_30;
              } else {
               goto zig_block_30;
              }
             }
             zig_block_30:;
             /* file:32:13 */
             /* file:32:29 */
             zig_u32 const t175 = t16;
             zig_usize const t176 = generator_getIdx(a0, t175, a2);
             zig_u8 * const t177 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_u8 * const t178 = &(t177)[t176];
             (*t178) = zig_as_u8(17);
             goto zig_block_15;
            } else {
             {
              /* file:34:19 */
              zig_u32 const t179 = t16;
              zig_T_tuple_7bu32_2c_20u1_7d t180;
              t180.f1 = zig_subo_u32(&t180.f0, t15, zig_as_u32(2), zig_as_u8(32));
              zig_u8 const t181 = t180.f1;
              zig_bool const t182 = t181 == zig_as_u8(0);
              {
               if (t182) {
                goto zig_block_34;
               } else {
                builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1247), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
               }
              }
              zig_block_34:;
              zig_u32 const t183 = t180.f0;
              zig_bool const t184 = t179 == t183;
              zig_bool t185;
              {
               if (t184) {
                t185 = zig_true;
                goto zig_block_35;
               } else {
                zig_u32 const t186 = t16;
                zig_T_tuple_7bu32_2c_20u1_7d t187;
                t187.f1 = zig_subo_u32(&t187.f0, t15, zig_as_u32(3), zig_as_u8(32));
                zig_u8 const t188 = t187.f1;
                zig_bool const t189 = t188 == zig_as_u8(0);
                {
                 if (t189) {
                  goto zig_block_36;
                 } else {
                  builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1248), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                 }
                }
                zig_block_36:;
                zig_u32 const t190 = t187.f0;
                zig_bool const t191 = t186 == t190;
                t185 = t191;
                goto zig_block_35;
               }
              }
              zig_block_35:;
              if (t185) {
               /* file:35:13 */
               /* file:35:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t192;
               t192.f1 = zig_subo_u32(&t192.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t193 = t192.f1;
               zig_bool const t194 = t193 == zig_as_u8(0);
               {
                if (t194) {
                 goto zig_block_37;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1249), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_37:;
               zig_u32 const t195 = t192.f0;
               zig_u32 const t196 = t16;
               zig_usize const t197 = generator_getIdx(t195, t196, a2);
               zig_u8 * const t198 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t199 = &(t198)[t197];
               (*t199) = zig_as_u8(18);
               /* file:36:13 */
               /* file:36:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t200;
               t200.f1 = zig_addo_u32(&t200.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t201 = t200.f1;
               zig_bool const t202 = t201 == zig_as_u8(0);
               {
                if (t202) {
                 goto zig_block_38;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1250), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_38:;
               zig_u32 const t203 = t200.f0;
               zig_u32 const t204 = t16;
               zig_usize const t205 = generator_getIdx(t203, t204, a2);
               zig_u8 * const t206 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t207 = &(t206)[t205];
               (*t207) = zig_as_u8(18);
               /* file:37:13 */
               /* file:37:29 */
               zig_u32 const t208 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t209;
               t209.f1 = zig_subo_u32(&t209.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t210 = t209.f1;
               zig_bool const t211 = t210 == zig_as_u8(0);
               {
                if (t211) {
                 goto zig_block_39;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1251), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_39:;
               zig_u32 const t212 = t209.f0;
               zig_usize const t213 = generator_getIdx(a0, t208, t212);
               zig_u8 * const t214 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t215 = &(t214)[t213];
               (*t215) = zig_as_u8(18);
               /* file:38:13 */
               /* file:38:29 */
               zig_u32 const t216 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t217;
               t217.f1 = zig_addo_u32(&t217.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t218 = t217.f1;
               zig_bool const t219 = t218 == zig_as_u8(0);
               {
                if (t219) {
                 goto zig_block_40;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1252), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_40:;
               zig_u32 const t220 = t217.f0;
               zig_usize const t221 = generator_getIdx(a0, t216, t220);
               zig_u8 * const t222 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t223 = &(t222)[t221];
               (*t223) = zig_as_u8(18);
               /* file:39:13 */
               /* file:39:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t224;
               t224.f1 = zig_subo_u32(&t224.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t225 = t224.f1;
               zig_bool const t226 = t225 == zig_as_u8(0);
               {
                if (t226) {
                 goto zig_block_41;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1253), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_41:;
               zig_u32 const t227 = t224.f0;
               zig_u32 const t228 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t229;
               t229.f1 = zig_subo_u32(&t229.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t230 = t229.f1;
               zig_bool const t231 = t230 == zig_as_u8(0);
               {
                if (t231) {
                 goto zig_block_42;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1254), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_42:;
               zig_u32 const t232 = t229.f0;
               zig_usize const t233 = generator_getIdx(t227, t228, t232);
               zig_u8 * const t234 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t235 = &(t234)[t233];
               (*t235) = zig_as_u8(18);
               /* file:40:13 */
               /* file:40:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t236;
               t236.f1 = zig_addo_u32(&t236.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t237 = t236.f1;
               zig_bool const t238 = t237 == zig_as_u8(0);
               {
                if (t238) {
                 goto zig_block_43;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1255), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_43:;
               zig_u32 const t239 = t236.f0;
               zig_u32 const t240 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t241;
               t241.f1 = zig_subo_u32(&t241.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t242 = t241.f1;
               zig_bool const t243 = t242 == zig_as_u8(0);
               {
                if (t243) {
                 goto zig_block_44;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1256), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_44:;
               zig_u32 const t244 = t241.f0;
               zig_usize const t245 = generator_getIdx(t239, t240, t244);
               zig_u8 * const t246 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t247 = &(t246)[t245];
               (*t247) = zig_as_u8(18);
               /* file:41:13 */
               /* file:41:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t248;
               t248.f1 = zig_subo_u32(&t248.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t249 = t248.f1;
               zig_bool const t250 = t249 == zig_as_u8(0);
               {
                if (t250) {
                 goto zig_block_45;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1257), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_45:;
               zig_u32 const t251 = t248.f0;
               zig_u32 const t252 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t253;
               t253.f1 = zig_addo_u32(&t253.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t254 = t253.f1;
               zig_bool const t255 = t254 == zig_as_u8(0);
               {
                if (t255) {
                 goto zig_block_46;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1258), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_46:;
               zig_u32 const t256 = t253.f0;
               zig_usize const t257 = generator_getIdx(t251, t252, t256);
               zig_u8 * const t258 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t259 = &(t258)[t257];
               (*t259) = zig_as_u8(18);
               /* file:42:13 */
               /* file:42:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t260;
               t260.f1 = zig_addo_u32(&t260.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t261 = t260.f1;
               zig_bool const t262 = t261 == zig_as_u8(0);
               {
                if (t262) {
                 goto zig_block_47;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1259), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_47:;
               zig_u32 const t263 = t260.f0;
               zig_u32 const t264 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t265;
               t265.f1 = zig_addo_u32(&t265.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t266 = t265.f1;
               zig_bool const t267 = t266 == zig_as_u8(0);
               {
                if (t267) {
                 goto zig_block_48;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1260), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_48:;
               zig_u32 const t268 = t265.f0;
               zig_usize const t269 = generator_getIdx(t263, t264, t268);
               zig_u8 * const t270 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t271 = &(t270)[t269];
               (*t271) = zig_as_u8(18);
               /* file:44:13 */
               /* file:44:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t272;
               t272.f1 = zig_subo_u32(&t272.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t273 = t272.f1;
               zig_bool const t274 = t273 == zig_as_u8(0);
               {
                if (t274) {
                 goto zig_block_49;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1261), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_49:;
               zig_u32 const t275 = t272.f0;
               zig_u32 const t276 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t277;
               t277.f1 = zig_subo_u32(&t277.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t278 = t277.f1;
               zig_bool const t279 = t278 == zig_as_u8(0);
               {
                if (t279) {
                 goto zig_block_50;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1262), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_50:;
               zig_u32 const t280 = t277.f0;
               zig_usize const t281 = generator_getIdx(t275, t276, t280);
               zig_u8 * const t282 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t283 = &(t282)[t281];
               (*t283) = zig_as_u8(18);
               /* file:45:13 */
               /* file:45:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t284;
               t284.f1 = zig_subo_u32(&t284.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t285 = t284.f1;
               zig_bool const t286 = t285 == zig_as_u8(0);
               {
                if (t286) {
                 goto zig_block_51;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1263), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_51:;
               zig_u32 const t287 = t284.f0;
               zig_u32 const t288 = t16;
               zig_usize const t289 = generator_getIdx(t287, t288, a2);
               zig_u8 * const t290 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t291 = &(t290)[t289];
               (*t291) = zig_as_u8(18);
               /* file:46:13 */
               /* file:46:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t292;
               t292.f1 = zig_subo_u32(&t292.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t293 = t292.f1;
               zig_bool const t294 = t293 == zig_as_u8(0);
               {
                if (t294) {
                 goto zig_block_52;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1264), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_52:;
               zig_u32 const t295 = t292.f0;
               zig_u32 const t296 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t297;
               t297.f1 = zig_addo_u32(&t297.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t298 = t297.f1;
               zig_bool const t299 = t298 == zig_as_u8(0);
               {
                if (t299) {
                 goto zig_block_53;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1265), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_53:;
               zig_u32 const t300 = t297.f0;
               zig_usize const t301 = generator_getIdx(t295, t296, t300);
               zig_u8 * const t302 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t303 = &(t302)[t301];
               (*t303) = zig_as_u8(18);
               /* file:48:13 */
               /* file:48:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t304;
               t304.f1 = zig_addo_u32(&t304.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t305 = t304.f1;
               zig_bool const t306 = t305 == zig_as_u8(0);
               {
                if (t306) {
                 goto zig_block_54;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1266), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_54:;
               zig_u32 const t307 = t304.f0;
               zig_u32 const t308 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t309;
               t309.f1 = zig_subo_u32(&t309.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t310 = t309.f1;
               zig_bool const t311 = t310 == zig_as_u8(0);
               {
                if (t311) {
                 goto zig_block_55;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1267), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_55:;
               zig_u32 const t312 = t309.f0;
               zig_usize const t313 = generator_getIdx(t307, t308, t312);
               zig_u8 * const t314 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t315 = &(t314)[t313];
               (*t315) = zig_as_u8(18);
               /* file:49:13 */
               /* file:49:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t316;
               t316.f1 = zig_addo_u32(&t316.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t317 = t316.f1;
               zig_bool const t318 = t317 == zig_as_u8(0);
               {
                if (t318) {
                 goto zig_block_56;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1268), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_56:;
               zig_u32 const t319 = t316.f0;
               zig_u32 const t320 = t16;
               zig_usize const t321 = generator_getIdx(t319, t320, a2);
               zig_u8 * const t322 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t323 = &(t322)[t321];
               (*t323) = zig_as_u8(18);
               /* file:50:13 */
               /* file:50:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t324;
               t324.f1 = zig_addo_u32(&t324.f0, a0, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t325 = t324.f1;
               zig_bool const t326 = t325 == zig_as_u8(0);
               {
                if (t326) {
                 goto zig_block_57;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1269), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_57:;
               zig_u32 const t327 = t324.f0;
               zig_u32 const t328 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t329;
               t329.f1 = zig_addo_u32(&t329.f0, a2, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t330 = t329.f1;
               zig_bool const t331 = t330 == zig_as_u8(0);
               {
                if (t331) {
                 goto zig_block_58;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1270), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_58:;
               zig_u32 const t332 = t329.f0;
               zig_usize const t333 = generator_getIdx(t327, t328, t332);
               zig_u8 * const t334 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t335 = &(t334)[t333];
               (*t335) = zig_as_u8(18);
               /* file:52:13 */
               /* file:52:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t336;
               t336.f1 = zig_subo_u32(&t336.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t337 = t336.f1;
               zig_bool const t338 = t337 == zig_as_u8(0);
               {
                if (t338) {
                 goto zig_block_59;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1271), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_59:;
               zig_u32 const t339 = t336.f0;
               zig_u32 const t340 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t341;
               t341.f1 = zig_addo_u32(&t341.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t342 = t341.f1;
               zig_bool const t343 = t342 == zig_as_u8(0);
               {
                if (t343) {
                 goto zig_block_60;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1272), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_60:;
               zig_u32 const t344 = t341.f0;
               zig_usize const t345 = generator_getIdx(t339, t340, t344);
               zig_u8 * const t346 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t347 = &(t346)[t345];
               (*t347) = zig_as_u8(18);
               /* file:53:13 */
               /* file:53:29 */
               zig_u32 const t348 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t349;
               t349.f1 = zig_addo_u32(&t349.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t350 = t349.f1;
               zig_bool const t351 = t350 == zig_as_u8(0);
               {
                if (t351) {
                 goto zig_block_61;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1273), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_61:;
               zig_u32 const t352 = t349.f0;
               zig_usize const t353 = generator_getIdx(a0, t348, t352);
               zig_u8 * const t354 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t355 = &(t354)[t353];
               (*t355) = zig_as_u8(18);
               /* file:54:13 */
               /* file:54:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t356;
               t356.f1 = zig_addo_u32(&t356.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t357 = t356.f1;
               zig_bool const t358 = t357 == zig_as_u8(0);
               {
                if (t358) {
                 goto zig_block_62;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1274), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_62:;
               zig_u32 const t359 = t356.f0;
               zig_u32 const t360 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t361;
               t361.f1 = zig_addo_u32(&t361.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t362 = t361.f1;
               zig_bool const t363 = t362 == zig_as_u8(0);
               {
                if (t363) {
                 goto zig_block_63;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1275), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_63:;
               zig_u32 const t364 = t361.f0;
               zig_usize const t365 = generator_getIdx(t359, t360, t364);
               zig_u8 * const t366 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t367 = &(t366)[t365];
               (*t367) = zig_as_u8(18);
               /* file:56:13 */
               /* file:56:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t368;
               t368.f1 = zig_subo_u32(&t368.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t369 = t368.f1;
               zig_bool const t370 = t369 == zig_as_u8(0);
               {
                if (t370) {
                 goto zig_block_64;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1276), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_64:;
               zig_u32 const t371 = t368.f0;
               zig_u32 const t372 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t373;
               t373.f1 = zig_subo_u32(&t373.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t374 = t373.f1;
               zig_bool const t375 = t374 == zig_as_u8(0);
               {
                if (t375) {
                 goto zig_block_65;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1277), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_65:;
               zig_u32 const t376 = t373.f0;
               zig_usize const t377 = generator_getIdx(t371, t372, t376);
               zig_u8 * const t378 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t379 = &(t378)[t377];
               (*t379) = zig_as_u8(18);
               /* file:57:13 */
               /* file:57:29 */
               zig_u32 const t380 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t381;
               t381.f1 = zig_subo_u32(&t381.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t382 = t381.f1;
               zig_bool const t383 = t382 == zig_as_u8(0);
               {
                if (t383) {
                 goto zig_block_66;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1278), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_66:;
               zig_u32 const t384 = t381.f0;
               zig_usize const t385 = generator_getIdx(a0, t380, t384);
               zig_u8 * const t386 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t387 = &(t386)[t385];
               (*t387) = zig_as_u8(18);
               /* file:58:13 */
               /* file:58:29 */
               zig_T_tuple_7bu32_2c_20u1_7d t388;
               t388.f1 = zig_addo_u32(&t388.f0, a0, zig_as_u32(1), zig_as_u8(32));
               zig_u8 const t389 = t388.f1;
               zig_bool const t390 = t389 == zig_as_u8(0);
               {
                if (t390) {
                 goto zig_block_67;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1279), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_67:;
               zig_u32 const t391 = t388.f0;
               zig_u32 const t392 = t16;
               zig_T_tuple_7bu32_2c_20u1_7d t393;
               t393.f1 = zig_subo_u32(&t393.f0, a2, zig_as_u32(2), zig_as_u8(32));
               zig_u8 const t394 = t393.f1;
               zig_bool const t395 = t394 == zig_as_u8(0);
               {
                if (t395) {
                 goto zig_block_68;
                } else {
                 builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1280), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                }
               }
               zig_block_68:;
               zig_u32 const t396 = t393.f0;
               zig_usize const t397 = generator_getIdx(t391, t392, t396);
               zig_u8 * const t398 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t399 = &(t398)[t397];
               (*t399) = zig_as_u8(18);
               /* file:61:16 */
               {
                /* file:61:31 */
                zig_S_rand_Random__343 const t400 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
                zig_S_rand_Random__343 t401;
                t401 = t400;
                zig_S_rand_Random__343 const * const t402 = (zig_S_rand_Random__343 const * )&t401;
                zig_S_rand_Random__343 const t403 = (*t402);
                /* file:61:37 */
                zig_usize const t404 = rand_Random_int__anon_712(t403);
                zig_usize const t405 = zig_mod_u32(t404, zig_as_u32(2));
                zig_u32 t406;
                memcpy(&t406, &t405, sizeof(zig_u32 ));
                t406 = zig_wrap_u32(t406, zig_as_u8(32));
                zig_bool const t407 = t406 == zig_as_u32(0);
                if (t407) {
                 /* file:62:17 */
                 /* file:62:33 */
                 zig_T_tuple_7bu32_2c_20u1_7d t408;
                 t408.f1 = zig_subo_u32(&t408.f0, a0, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t409 = t408.f1;
                 zig_bool const t410 = t409 == zig_as_u8(0);
                 {
                  if (t410) {
                   goto zig_block_70;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1281), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_70:;
                 zig_u32 const t411 = t408.f0;
                 zig_u32 const t412 = t16;
                 zig_T_tuple_7bu32_2c_20u1_7d t413;
                 t413.f1 = zig_subo_u32(&t413.f0, a2, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t414 = t413.f1;
                 zig_bool const t415 = t414 == zig_as_u8(0);
                 {
                  if (t415) {
                   goto zig_block_71;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1282), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_71:;
                 zig_u32 const t416 = t413.f0;
                 zig_usize const t417 = generator_getIdx(t411, t412, t416);
                 zig_u8 * const t418 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                 zig_u8 * const t419 = &(t418)[t417];
                 (*t419) = zig_as_u8(18);
                 goto zig_block_69;
                } else {
                 goto zig_block_69;
                }
               }
               zig_block_69:;
               /* file:64:16 */
               {
                /* file:64:31 */
                zig_S_rand_Random__343 const t420 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
                zig_S_rand_Random__343 t421;
                t421 = t420;
                zig_S_rand_Random__343 const * const t422 = (zig_S_rand_Random__343 const * )&t421;
                zig_S_rand_Random__343 const t423 = (*t422);
                /* file:64:37 */
                zig_usize const t424 = rand_Random_int__anon_712(t423);
                zig_usize const t425 = zig_mod_u32(t424, zig_as_u32(2));
                zig_u32 t426;
                memcpy(&t426, &t425, sizeof(zig_u32 ));
                t426 = zig_wrap_u32(t426, zig_as_u8(32));
                zig_bool const t427 = t426 == zig_as_u32(0);
                if (t427) {
                 /* file:65:17 */
                 /* file:65:33 */
                 zig_T_tuple_7bu32_2c_20u1_7d t428;
                 t428.f1 = zig_addo_u32(&t428.f0, a0, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t429 = t428.f1;
                 zig_bool const t430 = t429 == zig_as_u8(0);
                 {
                  if (t430) {
                   goto zig_block_73;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1283), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_73:;
                 zig_u32 const t431 = t428.f0;
                 zig_u32 const t432 = t16;
                 zig_T_tuple_7bu32_2c_20u1_7d t433;
                 t433.f1 = zig_subo_u32(&t433.f0, a2, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t434 = t433.f1;
                 zig_bool const t435 = t434 == zig_as_u8(0);
                 {
                  if (t435) {
                   goto zig_block_74;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1284), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_74:;
                 zig_u32 const t436 = t433.f0;
                 zig_usize const t437 = generator_getIdx(t431, t432, t436);
                 zig_u8 * const t438 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                 zig_u8 * const t439 = &(t438)[t437];
                 (*t439) = zig_as_u8(18);
                 goto zig_block_72;
                } else {
                 goto zig_block_72;
                }
               }
               zig_block_72:;
               /* file:67:16 */
               {
                /* file:67:31 */
                zig_S_rand_Random__343 const t440 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
                zig_S_rand_Random__343 t441;
                t441 = t440;
                zig_S_rand_Random__343 const * const t442 = (zig_S_rand_Random__343 const * )&t441;
                zig_S_rand_Random__343 const t443 = (*t442);
                /* file:67:37 */
                zig_usize const t444 = rand_Random_int__anon_712(t443);
                zig_usize const t445 = zig_mod_u32(t444, zig_as_u32(2));
                zig_u32 t446;
                memcpy(&t446, &t445, sizeof(zig_u32 ));
                t446 = zig_wrap_u32(t446, zig_as_u8(32));
                zig_bool const t447 = t446 == zig_as_u32(0);
                if (t447) {
                 /* file:68:17 */
                 /* file:68:33 */
                 zig_T_tuple_7bu32_2c_20u1_7d t448;
                 t448.f1 = zig_subo_u32(&t448.f0, a0, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t449 = t448.f1;
                 zig_bool const t450 = t449 == zig_as_u8(0);
                 {
                  if (t450) {
                   goto zig_block_76;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1285), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_76:;
                 zig_u32 const t451 = t448.f0;
                 zig_u32 const t452 = t16;
                 zig_T_tuple_7bu32_2c_20u1_7d t453;
                 t453.f1 = zig_addo_u32(&t453.f0, a2, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t454 = t453.f1;
                 zig_bool const t455 = t454 == zig_as_u8(0);
                 {
                  if (t455) {
                   goto zig_block_77;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1286), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_77:;
                 zig_u32 const t456 = t453.f0;
                 zig_usize const t457 = generator_getIdx(t451, t452, t456);
                 zig_u8 * const t458 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                 zig_u8 * const t459 = &(t458)[t457];
                 (*t459) = zig_as_u8(18);
                 goto zig_block_75;
                } else {
                 goto zig_block_75;
                }
               }
               zig_block_75:;
               /* file:70:16 */
               {
                /* file:70:31 */
                zig_S_rand_Random__343 const t460 = rand_Xoshiro256_random((zig_S_rand_Xoshiro256__255 * )((zig_S_rand_Xoshiro256__255 * )&generator_rnd));
                zig_S_rand_Random__343 t461;
                t461 = t460;
                zig_S_rand_Random__343 const * const t462 = (zig_S_rand_Random__343 const * )&t461;
                zig_S_rand_Random__343 const t463 = (*t462);
                /* file:70:37 */
                zig_usize const t464 = rand_Random_int__anon_712(t463);
                zig_usize const t465 = zig_mod_u32(t464, zig_as_u32(2));
                zig_u32 t466;
                memcpy(&t466, &t465, sizeof(zig_u32 ));
                t466 = zig_wrap_u32(t466, zig_as_u8(32));
                zig_bool const t467 = t466 == zig_as_u32(0);
                if (t467) {
                 /* file:71:17 */
                 /* file:71:33 */
                 zig_T_tuple_7bu32_2c_20u1_7d t468;
                 t468.f1 = zig_addo_u32(&t468.f0, a0, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t469 = t468.f1;
                 zig_bool const t470 = t469 == zig_as_u8(0);
                 {
                  if (t470) {
                   goto zig_block_79;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1287), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_79:;
                 zig_u32 const t471 = t468.f0;
                 zig_u32 const t472 = t16;
                 zig_T_tuple_7bu32_2c_20u1_7d t473;
                 t473.f1 = zig_addo_u32(&t473.f0, a2, zig_as_u32(2), zig_as_u8(32));
                 zig_u8 const t474 = t473.f1;
                 zig_bool const t475 = t474 == zig_as_u8(0);
                 {
                  if (t475) {
                   goto zig_block_80;
                  } else {
                   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1288), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
                  }
                 }
                 zig_block_80:;
                 zig_u32 const t476 = t473.f0;
                 zig_usize const t477 = generator_getIdx(t471, t472, t476);
                 zig_u8 * const t478 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
                 zig_u8 * const t479 = &(t478)[t477];
                 (*t479) = zig_as_u8(18);
                 goto zig_block_78;
                } else {
                 goto zig_block_78;
                }
               }
               zig_block_78:;
               /* file:73:13 */
               /* file:73:29 */
               zig_u32 const t480 = t16;
               zig_usize const t481 = generator_getIdx(a0, t480, a2);
               zig_u8 * const t482 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t483 = &(t482)[t481];
               (*t483) = zig_as_u8(17);
               goto zig_block_33;
              } else {
               /* file:76:13 */
               /* file:76:29 */
               zig_u32 const t484 = t16;
               zig_usize const t485 = generator_getIdx(a0, t484, a2);
               zig_u8 * const t486 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
               zig_u8 * const t487 = &(t486)[t485];
               (*t487) = zig_as_u8(17);
               goto zig_block_33;
              }
             }
             zig_block_33:;
             goto zig_block_15;
            }
           }
           zig_block_15:;
           goto zig_block_10;
          }
         }
         zig_block_10:;
         /* file:7:22 */
         zig_u32 const t488 = t16;
         zig_T_tuple_7bu32_2c_20u1_7d t489;
         t489.f1 = zig_subo_u32(&t489.f0, t488, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t490 = t489.f1;
         zig_bool const t491 = t490 == zig_as_u8(0);
         {
          if (t491) {
           goto zig_block_81;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_growTree__anon_1289), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_81:;
         zig_u32 const t492 = t489.f0;
         t16 = t492;
         goto zig_block_9;
        } else {
         goto zig_block_8;
        }
       }
       zig_block_9:;
      }
     }
     zig_block_8:;
     /* file:79:5 */
     /* file:79:5 */
     return zig_true;
    } else {
     goto zig_block_6;
    }
   }
   zig_block_6:;
   goto zig_block_0;
  } else {
   goto zig_block_0;
  }
 }
 zig_block_0:;
 /* file:83:5 */
 /* file:83:5 */
 return zig_false;
}

static zig_f64 perlin_noise(zig_f64 const a0, zig_f64 const a1, zig_f64 const a2) {
 static zig_usize const t40[zig_as_u32(512)] = {zig_as_u32(151),zig_as_u32(160),zig_as_u32(137),zig_as_u32(91),zig_as_u32(90),zig_as_u32(15),zig_as_u32(131),zig_as_u32(13),zig_as_u32(201),zig_as_u32(95),zig_as_u32(96),zig_as_u32(53),zig_as_u32(194),zig_as_u32(233),zig_as_u32(7),zig_as_u32(225),zig_as_u32(140),zig_as_u32(36),zig_as_u32(103),zig_as_u32(30),zig_as_u32(69),zig_as_u32(142),zig_as_u32(8),zig_as_u32(99),zig_as_u32(37),zig_as_u32(240),zig_as_u32(21),zig_as_u32(10),zig_as_u32(23),zig_as_u32(190),zig_as_u32(6),zig_as_u32(148),zig_as_u32(247),zig_as_u32(120),zig_as_u32(234),zig_as_u32(75),zig_as_u32(0),zig_as_u32(26),zig_as_u32(197),zig_as_u32(62),zig_as_u32(94),zig_as_u32(252),zig_as_u32(219),zig_as_u32(203),zig_as_u32(117),zig_as_u32(35),zig_as_u32(11),zig_as_u32(32),zig_as_u32(57),zig_as_u32(177),zig_as_u32(33),zig_as_u32(88),zig_as_u32(237),zig_as_u32(149),zig_as_u32(56),zig_as_u32(87),zig_as_u32(174),zig_as_u32(20),zig_as_u32(125),zig_as_u32(136),zig_as_u32(171),zig_as_u32(168),zig_as_u32(68),zig_as_u32(175),zig_as_u32(74),zig_as_u32(165),zig_as_u32(71),zig_as_u32(134),zig_as_u32(139),zig_as_u32(48),zig_as_u32(27),zig_as_u32(166),zig_as_u32(77),zig_as_u32(146),zig_as_u32(158),zig_as_u32(231),zig_as_u32(83),zig_as_u32(111),zig_as_u32(229),zig_as_u32(122),zig_as_u32(60),zig_as_u32(211),zig_as_u32(133),zig_as_u32(230),zig_as_u32(220),zig_as_u32(105),zig_as_u32(92),zig_as_u32(41),zig_as_u32(55),zig_as_u32(46),zig_as_u32(245),zig_as_u32(40),zig_as_u32(244),zig_as_u32(102),zig_as_u32(143),zig_as_u32(54),zig_as_u32(65),zig_as_u32(25),zig_as_u32(63),zig_as_u32(161),zig_as_u32(1),zig_as_u32(216),zig_as_u32(80),zig_as_u32(73),zig_as_u32(209),zig_as_u32(76),zig_as_u32(132),zig_as_u32(187),zig_as_u32(208),zig_as_u32(89),zig_as_u32(18),zig_as_u32(169),zig_as_u32(200),zig_as_u32(196),zig_as_u32(135),zig_as_u32(130),zig_as_u32(116),zig_as_u32(188),zig_as_u32(159),zig_as_u32(86),zig_as_u32(164),zig_as_u32(100),zig_as_u32(109),zig_as_u32(198),zig_as_u32(173),zig_as_u32(186),zig_as_u32(3),zig_as_u32(64),zig_as_u32(52),zig_as_u32(217),zig_as_u32(226),zig_as_u32(250),zig_as_u32(124),zig_as_u32(123),zig_as_u32(5),zig_as_u32(202),zig_as_u32(38),zig_as_u32(147),zig_as_u32(118),zig_as_u32(126),zig_as_u32(255),zig_as_u32(82),zig_as_u32(85),zig_as_u32(212),zig_as_u32(207),zig_as_u32(206),zig_as_u32(59),zig_as_u32(227),zig_as_u32(47),zig_as_u32(16),zig_as_u32(58),zig_as_u32(17),zig_as_u32(182),zig_as_u32(189),zig_as_u32(28),zig_as_u32(42),zig_as_u32(223),zig_as_u32(183),zig_as_u32(170),zig_as_u32(213),zig_as_u32(119),zig_as_u32(248),zig_as_u32(152),zig_as_u32(2),zig_as_u32(44),zig_as_u32(154),zig_as_u32(163),zig_as_u32(70),zig_as_u32(221),zig_as_u32(153),zig_as_u32(101),zig_as_u32(155),zig_as_u32(167),zig_as_u32(43),zig_as_u32(172),zig_as_u32(9),zig_as_u32(129),zig_as_u32(22),zig_as_u32(39),zig_as_u32(253),zig_as_u32(19),zig_as_u32(98),zig_as_u32(108),zig_as_u32(110),zig_as_u32(79),zig_as_u32(113),zig_as_u32(224),zig_as_u32(232),zig_as_u32(178),zig_as_u32(185),zig_as_u32(112),zig_as_u32(104),zig_as_u32(218),zig_as_u32(246),zig_as_u32(97),zig_as_u32(228),zig_as_u32(251),zig_as_u32(34),zig_as_u32(242),zig_as_u32(193),zig_as_u32(238),zig_as_u32(210),zig_as_u32(144),zig_as_u32(12),zig_as_u32(191),zig_as_u32(179),zig_as_u32(162),zig_as_u32(241),zig_as_u32(81),zig_as_u32(51),zig_as_u32(145),zig_as_u32(235),zig_as_u32(249),zig_as_u32(14),zig_as_u32(239),zig_as_u32(107),zig_as_u32(49),zig_as_u32(192),zig_as_u32(214),zig_as_u32(31),zig_as_u32(181),zig_as_u32(199),zig_as_u32(106),zig_as_u32(157),zig_as_u32(184),zig_as_u32(84),zig_as_u32(204),zig_as_u32(176),zig_as_u32(115),zig_as_u32(121),zig_as_u32(50),zig_as_u32(45),zig_as_u32(127),zig_as_u32(4),zig_as_u32(150),zig_as_u32(254),zig_as_u32(138),zig_as_u32(236),zig_as_u32(205),zig_as_u32(93),zig_as_u32(222),zig_as_u32(114),zig_as_u32(67),zig_as_u32(29),zig_as_u32(24),zig_as_u32(72),zig_as_u32(243),zig_as_u32(141),zig_as_u32(128),zig_as_u32(195),zig_as_u32(78),zig_as_u32(66),zig_as_u32(215),zig_as_u32(61),zig_as_u32(156),zig_as_u32(180),zig_as_u32(151),zig_as_u32(160),zig_as_u32(137),zig_as_u32(91),zig_as_u32(90),zig_as_u32(15),zig_as_u32(131),zig_as_u32(13),zig_as_u32(201),zig_as_u32(95),zig_as_u32(96),zig_as_u32(53),zig_as_u32(194),zig_as_u32(233),zig_as_u32(7),zig_as_u32(225),zig_as_u32(140),zig_as_u32(36),zig_as_u32(103),zig_as_u32(30),zig_as_u32(69),zig_as_u32(142),zig_as_u32(8),zig_as_u32(99),zig_as_u32(37),zig_as_u32(240),zig_as_u32(21),zig_as_u32(10),zig_as_u32(23),zig_as_u32(190),zig_as_u32(6),zig_as_u32(148),zig_as_u32(247),zig_as_u32(120),zig_as_u32(234),zig_as_u32(75),zig_as_u32(0),zig_as_u32(26),zig_as_u32(197),zig_as_u32(62),zig_as_u32(94),zig_as_u32(252),zig_as_u32(219),zig_as_u32(203),zig_as_u32(117),zig_as_u32(35),zig_as_u32(11),zig_as_u32(32),zig_as_u32(57),zig_as_u32(177),zig_as_u32(33),zig_as_u32(88),zig_as_u32(237),zig_as_u32(149),zig_as_u32(56),zig_as_u32(87),zig_as_u32(174),zig_as_u32(20),zig_as_u32(125),zig_as_u32(136),zig_as_u32(171),zig_as_u32(168),zig_as_u32(68),zig_as_u32(175),zig_as_u32(74),zig_as_u32(165),zig_as_u32(71),zig_as_u32(134),zig_as_u32(139),zig_as_u32(48),zig_as_u32(27),zig_as_u32(166),zig_as_u32(77),zig_as_u32(146),zig_as_u32(158),zig_as_u32(231),zig_as_u32(83),zig_as_u32(111),zig_as_u32(229),zig_as_u32(122),zig_as_u32(60),zig_as_u32(211),zig_as_u32(133),zig_as_u32(230),zig_as_u32(220),zig_as_u32(105),zig_as_u32(92),zig_as_u32(41),zig_as_u32(55),zig_as_u32(46),zig_as_u32(245),zig_as_u32(40),zig_as_u32(244),zig_as_u32(102),zig_as_u32(143),zig_as_u32(54),zig_as_u32(65),zig_as_u32(25),zig_as_u32(63),zig_as_u32(161),zig_as_u32(1),zig_as_u32(216),zig_as_u32(80),zig_as_u32(73),zig_as_u32(209),zig_as_u32(76),zig_as_u32(132),zig_as_u32(187),zig_as_u32(208),zig_as_u32(89),zig_as_u32(18),zig_as_u32(169),zig_as_u32(200),zig_as_u32(196),zig_as_u32(135),zig_as_u32(130),zig_as_u32(116),zig_as_u32(188),zig_as_u32(159),zig_as_u32(86),zig_as_u32(164),zig_as_u32(100),zig_as_u32(109),zig_as_u32(198),zig_as_u32(173),zig_as_u32(186),zig_as_u32(3),zig_as_u32(64),zig_as_u32(52),zig_as_u32(217),zig_as_u32(226),zig_as_u32(250),zig_as_u32(124),zig_as_u32(123),zig_as_u32(5),zig_as_u32(202),zig_as_u32(38),zig_as_u32(147),zig_as_u32(118),zig_as_u32(126),zig_as_u32(255),zig_as_u32(82),zig_as_u32(85),zig_as_u32(212),zig_as_u32(207),zig_as_u32(206),zig_as_u32(59),zig_as_u32(227),zig_as_u32(47),zig_as_u32(16),zig_as_u32(58),zig_as_u32(17),zig_as_u32(182),zig_as_u32(189),zig_as_u32(28),zig_as_u32(42),zig_as_u32(223),zig_as_u32(183),zig_as_u32(170),zig_as_u32(213),zig_as_u32(119),zig_as_u32(248),zig_as_u32(152),zig_as_u32(2),zig_as_u32(44),zig_as_u32(154),zig_as_u32(163),zig_as_u32(70),zig_as_u32(221),zig_as_u32(153),zig_as_u32(101),zig_as_u32(155),zig_as_u32(167),zig_as_u32(43),zig_as_u32(172),zig_as_u32(9),zig_as_u32(129),zig_as_u32(22),zig_as_u32(39),zig_as_u32(253),zig_as_u32(19),zig_as_u32(98),zig_as_u32(108),zig_as_u32(110),zig_as_u32(79),zig_as_u32(113),zig_as_u32(224),zig_as_u32(232),zig_as_u32(178),zig_as_u32(185),zig_as_u32(112),zig_as_u32(104),zig_as_u32(218),zig_as_u32(246),zig_as_u32(97),zig_as_u32(228),zig_as_u32(251),zig_as_u32(34),zig_as_u32(242),zig_as_u32(193),zig_as_u32(238),zig_as_u32(210),zig_as_u32(144),zig_as_u32(12),zig_as_u32(191),zig_as_u32(179),zig_as_u32(162),zig_as_u32(241),zig_as_u32(81),zig_as_u32(51),zig_as_u32(145),zig_as_u32(235),zig_as_u32(249),zig_as_u32(14),zig_as_u32(239),zig_as_u32(107),zig_as_u32(49),zig_as_u32(192),zig_as_u32(214),zig_as_u32(31),zig_as_u32(181),zig_as_u32(199),zig_as_u32(106),zig_as_u32(157),zig_as_u32(184),zig_as_u32(84),zig_as_u32(204),zig_as_u32(176),zig_as_u32(115),zig_as_u32(121),zig_as_u32(50),zig_as_u32(45),zig_as_u32(127),zig_as_u32(4),zig_as_u32(150),zig_as_u32(254),zig_as_u32(138),zig_as_u32(236),zig_as_u32(205),zig_as_u32(93),zig_as_u32(222),zig_as_u32(114),zig_as_u32(67),zig_as_u32(29),zig_as_u32(24),zig_as_u32(72),zig_as_u32(243),zig_as_u32(141),zig_as_u32(128),zig_as_u32(195),zig_as_u32(78),zig_as_u32(66),zig_as_u32(215),zig_as_u32(61),zig_as_u32(156),zig_as_u32(180)};
 /* file:2:5 */
 zig_f64 const t0 = zig_libc_name_f64(floor)(a0);
 zig_isize const t1 = zig_wrap_i32(__fixdfsi(t0), zig_as_u8(32));
 zig_f64 const t2 = __floatsidf(t1);
 zig_f64 const t3 = zig_sub_f64(t0, t2);
 zig_bool const t4 = zig_lt_f64(t3, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000))) < zig_as_i8(0);
 zig_bool const t5 = zig_gt_f64(t3, (zig_f64 )zig_as_f64(-0x1p0, -zig_as_i64(0x4010000000000000))) > zig_as_i8(0);
 zig_bool const t6 = t4 & t5;
 {
  if (t6) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1290), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_isize const t7 = t1 & zig_as_i32(255);
 zig_bool const t8 = t7 >= zig_as_i32(0);
 {
  if (t8) {
   goto zig_block_1;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1291), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_1:;
 zig_usize const t9 = (zig_usize )t7;
 /* var:x_int */
 /* file:3:5 */
 zig_f64 const t10 = zig_libc_name_f64(floor)(a1);
 zig_isize const t11 = zig_wrap_i32(__fixdfsi(t10), zig_as_u8(32));
 zig_f64 const t12 = __floatsidf(t11);
 zig_f64 const t13 = zig_sub_f64(t10, t12);
 zig_bool const t14 = zig_lt_f64(t13, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000))) < zig_as_i8(0);
 zig_bool const t15 = zig_gt_f64(t13, (zig_f64 )zig_as_f64(-0x1p0, -zig_as_i64(0x4010000000000000))) > zig_as_i8(0);
 zig_bool const t16 = t14 & t15;
 {
  if (t16) {
   goto zig_block_2;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1292), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_2:;
 zig_isize const t17 = t11 & zig_as_i32(255);
 zig_bool const t18 = t17 >= zig_as_i32(0);
 {
  if (t18) {
   goto zig_block_3;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1293), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_3:;
 zig_usize const t19 = (zig_usize )t17;
 /* var:y_int */
 /* file:4:5 */
 zig_f64 const t20 = zig_libc_name_f64(floor)(a2);
 zig_isize const t21 = zig_wrap_i32(__fixdfsi(t20), zig_as_u8(32));
 zig_f64 const t22 = __floatsidf(t21);
 zig_f64 const t23 = zig_sub_f64(t20, t22);
 zig_bool const t24 = zig_lt_f64(t23, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000))) < zig_as_i8(0);
 zig_bool const t25 = zig_gt_f64(t23, (zig_f64 )zig_as_f64(-0x1p0, -zig_as_i64(0x4010000000000000))) > zig_as_i8(0);
 zig_bool const t26 = t24 & t25;
 {
  if (t26) {
   goto zig_block_4;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1294), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_4:;
 zig_isize const t27 = t21 & zig_as_i32(255);
 zig_bool const t28 = t27 >= zig_as_i32(0);
 {
  if (t28) {
   goto zig_block_5;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1295), zig_as_u32(50)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_5:;
 zig_usize const t29 = (zig_usize )t27;
 /* var:z_int */
 /* file:6:5 */
 zig_f64 const t30 = zig_libc_name_f64(floor)(a0);
 zig_f64 const t31 = zig_sub_f64(a0, t30);
 /* var:x_float */
 /* file:7:5 */
 zig_f64 const t32 = zig_libc_name_f64(floor)(a1);
 zig_f64 const t33 = zig_sub_f64(a1, t32);
 /* var:y_float */
 /* file:8:5 */
 zig_f64 const t34 = zig_libc_name_f64(floor)(a2);
 zig_f64 const t35 = zig_sub_f64(a2, t34);
 /* var:z_float */
 /* file:10:5 */
 /* file:10:19 */
 zig_f64 const t36 = perlin_fade(t31);
 /* var:u */
 /* file:11:5 */
 /* file:11:19 */
 zig_f64 const t37 = perlin_fade(t33);
 /* var:v */
 /* file:12:5 */
 /* file:12:19 */
 zig_f64 const t38 = perlin_fade(t35);
 /* var:w */
 /* file:14:5 */
 zig_bool const t39 = t9 < zig_as_u32(512);
 {
  if (t39) {
   goto zig_block_6;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_6:;
 zig_usize const t41 = t40[t9];
 zig_T_tuple_7busize_2c_20u1_7d t42;
 t42.f1 = zig_addo_u32(&t42.f0, t41, t19, zig_as_u8(32));
 zig_u8 const t43 = t42.f1;
 zig_bool const t44 = t43 == zig_as_u8(0);
 {
  if (t44) {
   goto zig_block_7;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1296), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_7:;
 zig_usize const t45 = t42.f0;
 /* var:a */
 /* file:15:5 */
 zig_bool const t46 = t45 < zig_as_u32(512);
 {
  if (t46) {
   goto zig_block_8;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_8:;
 zig_usize const t47 = t40[t45];
 zig_T_tuple_7busize_2c_20u1_7d t48;
 t48.f1 = zig_addo_u32(&t48.f0, t47, t29, zig_as_u8(32));
 zig_u8 const t49 = t48.f1;
 zig_bool const t50 = t49 == zig_as_u8(0);
 {
  if (t50) {
   goto zig_block_9;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1297), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_9:;
 zig_usize const t51 = t48.f0;
 /* var:aa */
 /* file:16:5 */
 zig_T_tuple_7busize_2c_20u1_7d t52;
 t52.f1 = zig_addo_u32(&t52.f0, t45, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t53 = t52.f1;
 zig_bool const t54 = t53 == zig_as_u8(0);
 {
  if (t54) {
   goto zig_block_10;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1298), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_10:;
 zig_usize const t55 = t52.f0;
 zig_bool const t56 = t55 < zig_as_u32(512);
 {
  if (t56) {
   goto zig_block_11;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_11:;
 zig_usize const t57 = t40[t55];
 zig_T_tuple_7busize_2c_20u1_7d t58;
 t58.f1 = zig_addo_u32(&t58.f0, t57, t29, zig_as_u8(32));
 zig_u8 const t59 = t58.f1;
 zig_bool const t60 = t59 == zig_as_u8(0);
 {
  if (t60) {
   goto zig_block_12;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1299), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_12:;
 zig_usize const t61 = t58.f0;
 /* var:ab */
 /* file:17:5 */
 zig_T_tuple_7busize_2c_20u1_7d t62;
 t62.f1 = zig_addo_u32(&t62.f0, t9, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t63 = t62.f1;
 zig_bool const t64 = t63 == zig_as_u8(0);
 {
  if (t64) {
   goto zig_block_13;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1300), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_13:;
 zig_usize const t65 = t62.f0;
 zig_bool const t66 = t65 < zig_as_u32(512);
 {
  if (t66) {
   goto zig_block_14;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_14:;
 zig_usize const t67 = t40[t65];
 zig_T_tuple_7busize_2c_20u1_7d t68;
 t68.f1 = zig_addo_u32(&t68.f0, t67, t19, zig_as_u8(32));
 zig_u8 const t69 = t68.f1;
 zig_bool const t70 = t69 == zig_as_u8(0);
 {
  if (t70) {
   goto zig_block_15;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1301), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_15:;
 zig_usize const t71 = t68.f0;
 /* var:b */
 /* file:18:5 */
 zig_bool const t72 = t71 < zig_as_u32(512);
 {
  if (t72) {
   goto zig_block_16;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_16:;
 zig_usize const t73 = t40[t71];
 zig_T_tuple_7busize_2c_20u1_7d t74;
 t74.f1 = zig_addo_u32(&t74.f0, t73, t29, zig_as_u8(32));
 zig_u8 const t75 = t74.f1;
 zig_bool const t76 = t75 == zig_as_u8(0);
 {
  if (t76) {
   goto zig_block_17;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1302), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_17:;
 zig_usize const t77 = t74.f0;
 /* var:ba */
 /* file:19:5 */
 zig_T_tuple_7busize_2c_20u1_7d t78;
 t78.f1 = zig_addo_u32(&t78.f0, t71, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t79 = t78.f1;
 zig_bool const t80 = t79 == zig_as_u8(0);
 {
  if (t80) {
   goto zig_block_18;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1303), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_18:;
 zig_usize const t81 = t78.f0;
 zig_bool const t82 = t81 < zig_as_u32(512);
 {
  if (t82) {
   goto zig_block_19;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_19:;
 zig_usize const t83 = t40[t81];
 zig_T_tuple_7busize_2c_20u1_7d t84;
 t84.f1 = zig_addo_u32(&t84.f0, t83, t29, zig_as_u8(32));
 zig_u8 const t85 = t84.f1;
 zig_bool const t86 = t85 == zig_as_u8(0);
 {
  if (t86) {
   goto zig_block_20;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1304), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_20:;
 zig_usize const t87 = t84.f0;
 /* var:bb */
 /* file:21:5 */
 zig_f64 t88;
 /* file:21:16 */
 /* file:21:24 */
 /* file:21:32 */
 /* file:21:40 */
 zig_bool const t89 = t51 < zig_as_u32(512);
 {
  if (t89) {
   goto zig_block_21;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_21:;
 zig_usize const t90 = t40[t51];
 zig_f64 const t91 = grad(t90, t31, t33, t35);
 /* file:22:13 */
 zig_bool const t92 = t77 < zig_as_u32(512);
 {
  if (t92) {
   goto zig_block_22;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_22:;
 zig_usize const t93 = t40[t77];
 zig_f64 const t94 = zig_sub_f64(t31, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t95 = grad(t93, t94, t33, t35);
 zig_f64 const t96 = perlin_lerp(t36, t91, t95);
 /* file:23:13 */
 /* file:23:21 */
 zig_bool const t97 = t61 < zig_as_u32(512);
 {
  if (t97) {
   goto zig_block_23;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_23:;
 zig_usize const t98 = t40[t61];
 zig_f64 const t99 = zig_sub_f64(t33, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t100 = grad(t98, t31, t99, t35);
 /* file:24:17 */
 zig_bool const t101 = t87 < zig_as_u32(512);
 {
  if (t101) {
   goto zig_block_24;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_24:;
 zig_usize const t102 = t40[t87];
 zig_f64 const t103 = zig_sub_f64(t31, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t104 = zig_sub_f64(t33, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t105 = grad(t102, t103, t104, t35);
 zig_f64 const t106 = perlin_lerp(t36, t100, t105);
 zig_f64 const t107 = perlin_lerp(t37, t96, t106);
 /* file:25:13 */
 /* file:25:21 */
 /* file:25:29 */
 zig_T_tuple_7busize_2c_20u1_7d t108;
 t108.f1 = zig_addo_u32(&t108.f0, t51, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t109 = t108.f1;
 zig_bool const t110 = t109 == zig_as_u8(0);
 {
  if (t110) {
   goto zig_block_25;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1305), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_25:;
 zig_usize const t111 = t108.f0;
 zig_bool const t112 = t111 < zig_as_u32(512);
 {
  if (t112) {
   goto zig_block_26;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_26:;
 zig_usize const t113 = t40[t111];
 zig_f64 const t114 = zig_sub_f64(t35, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t115 = grad(t113, t31, t33, t114);
 /* file:26:17 */
 zig_T_tuple_7busize_2c_20u1_7d t116;
 t116.f1 = zig_addo_u32(&t116.f0, t77, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t117 = t116.f1;
 zig_bool const t118 = t117 == zig_as_u8(0);
 {
  if (t118) {
   goto zig_block_27;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1306), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_27:;
 zig_usize const t119 = t116.f0;
 zig_bool const t120 = t119 < zig_as_u32(512);
 {
  if (t120) {
   goto zig_block_28;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_28:;
 zig_usize const t121 = t40[t119];
 zig_f64 const t122 = zig_sub_f64(t31, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t123 = zig_sub_f64(t35, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t124 = grad(t121, t122, t33, t123);
 zig_f64 const t125 = perlin_lerp(t36, t115, t124);
 /* file:27:21 */
 /* file:27:29 */
 zig_T_tuple_7busize_2c_20u1_7d t126;
 t126.f1 = zig_addo_u32(&t126.f0, t61, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t127 = t126.f1;
 zig_bool const t128 = t127 == zig_as_u8(0);
 {
  if (t128) {
   goto zig_block_29;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1307), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_29:;
 zig_usize const t129 = t126.f0;
 zig_bool const t130 = t129 < zig_as_u32(512);
 {
  if (t130) {
   goto zig_block_30;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_30:;
 zig_usize const t131 = t40[t129];
 zig_f64 const t132 = zig_sub_f64(t33, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t133 = zig_sub_f64(t35, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t134 = grad(t131, t31, t132, t133);
 /* file:28:26 */
 zig_T_tuple_7busize_2c_20u1_7d t135;
 t135.f1 = zig_addo_u32(&t135.f0, t87, zig_as_u32(1), zig_as_u8(32));
 zig_u8 const t136 = t135.f1;
 zig_bool const t137 = t136 == zig_as_u8(0);
 {
  if (t137) {
   goto zig_block_31;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&perlin_noise__anon_1308), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_31:;
 zig_usize const t138 = t135.f0;
 zig_bool const t139 = t138 < zig_as_u32(512);
 {
  if (t139) {
   goto zig_block_32;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_32:;
 zig_usize const t140 = t40[t138];
 zig_f64 const t141 = zig_sub_f64(t31, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t142 = zig_sub_f64(t33, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t143 = zig_sub_f64(t35, (zig_f64 )zig_as_f64(0x1p0, zig_as_i64(0x3ff0000000000000)));
 zig_f64 const t144 = grad(t140, t141, t142, t143);
 zig_f64 const t145 = perlin_lerp(t36, t134, t144);
 zig_f64 const t146 = perlin_lerp(t37, t125, t145);
 zig_f64 const t147 = perlin_lerp(t38, t107, t146);
 t88 = t147;
 /* file:21:5 */
 return t88;
}

static zig_void rand_Xoshiro256_fill(zig_S_rand_Xoshiro256__255 * const a0, zig_L_u8 const a1) {
 /* file:2:5 */
 zig_usize t0;
 t0 = zig_as_u32(0);
 /* var:i */
 /* file:3:5 */
 zig_usize const t1 = a1.len;
 zig_usize const t2 = a1.len;
 zig_usize const t3 = t2 & zig_as_u32(7);
 zig_T_tuple_7busize_2c_20u1_7d t4;
 t4.f1 = zig_subo_u32(&t4.f0, t1, t3, zig_as_u8(32));
 zig_u8 const t5 = t4.f1;
 zig_bool const t6 = t5 == zig_as_u8(0);
 {
  if (t6) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1309), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_usize const t7 = t4.f0;
 /* var:aligned_len */
 {
  while (zig_true) {
   {
    /* file:6:12 */
    zig_usize const t8 = t0;
    zig_u32 t9;
    memcpy(&t9, &t8, sizeof(zig_u32 ));
    t9 = zig_wrap_u32(t9, zig_as_u8(32));
    zig_u32 t10;
    memcpy(&t10, &t7, sizeof(zig_u32 ));
    t10 = zig_wrap_u32(t10, zig_as_u8(32));
    zig_bool const t11 = t9 < t10;
    if (t11) {
     /* file:6:40 */
     /* file:7:9 */
     zig_u64 t12;
     zig_S_rand_Xoshiro256__255 * t13;
     t13 = a0;
     zig_S_rand_Xoshiro256__255 * const * const t14 = (zig_S_rand_Xoshiro256__255 * const * )&t13;
     zig_S_rand_Xoshiro256__255 * const t15 = (*t14);
     /* file:7:26 */
     zig_u64 const t16 = rand_Xoshiro256_next(t15);
     zig_u64 * const t17 = (zig_u64 * )&t12;
     (*t17) = t16;
     /* var:n */
     /* file:8:9 */
     /* var:j */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t18;
     t18 = a1;
     zig_L_u8 const * const t19 = (zig_L_u8 const * )&t18;
     zig_usize const t20 = t0;
     zig_L_u8 const t21 = (*t19);
     zig_usize const t22 = t21.len;
     zig_bool const t23 = t20 < t22;
     {
      if (t23) {
       goto zig_block_3;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_3:;
     zig_u8 * const t24 = &t21.ptr[t20];
     zig_u64 const t25 = t12;
     zig_u8 const t26 = (zig_u8 )t25;
     (*t24) = t26;
     /* file:11:13 */
     zig_u64 const t27 = t12;
     zig_u64 const t28 = zig_shr_u64(t27, zig_as_u8(8));
     t12 = t28;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t29;
     t29 = a1;
     zig_L_u8 const * const t30 = (zig_L_u8 const * )&t29;
     zig_usize const t31 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t32;
     t32.f1 = zig_addo_u32(&t32.f0, t31, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t33 = t32.f1;
     zig_bool const t34 = t33 == zig_as_u8(0);
     {
      if (t34) {
       goto zig_block_4;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1311), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_4:;
     zig_usize const t35 = t32.f0;
     zig_L_u8 const t36 = (*t30);
     zig_usize const t37 = t36.len;
     zig_bool const t38 = t35 < t37;
     {
      if (t38) {
       goto zig_block_5;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_5:;
     zig_u8 * const t39 = &t36.ptr[t35];
     zig_u64 const t40 = t12;
     zig_u8 const t41 = (zig_u8 )t40;
     (*t39) = t41;
     /* file:11:13 */
     zig_u64 const t42 = t12;
     zig_u64 const t43 = zig_shr_u64(t42, zig_as_u8(8));
     t12 = t43;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t44;
     t44 = a1;
     zig_L_u8 const * const t45 = (zig_L_u8 const * )&t44;
     zig_usize const t46 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t47;
     t47.f1 = zig_addo_u32(&t47.f0, t46, zig_as_u32(2), zig_as_u8(32));
     zig_u8 const t48 = t47.f1;
     zig_bool const t49 = t48 == zig_as_u8(0);
     {
      if (t49) {
       goto zig_block_6;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1312), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_6:;
     zig_usize const t50 = t47.f0;
     zig_L_u8 const t51 = (*t45);
     zig_usize const t52 = t51.len;
     zig_bool const t53 = t50 < t52;
     {
      if (t53) {
       goto zig_block_7;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_7:;
     zig_u8 * const t54 = &t51.ptr[t50];
     zig_u64 const t55 = t12;
     zig_u8 const t56 = (zig_u8 )t55;
     (*t54) = t56;
     /* file:11:13 */
     zig_u64 const t57 = t12;
     zig_u64 const t58 = zig_shr_u64(t57, zig_as_u8(8));
     t12 = t58;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t59;
     t59 = a1;
     zig_L_u8 const * const t60 = (zig_L_u8 const * )&t59;
     zig_usize const t61 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t62;
     t62.f1 = zig_addo_u32(&t62.f0, t61, zig_as_u32(3), zig_as_u8(32));
     zig_u8 const t63 = t62.f1;
     zig_bool const t64 = t63 == zig_as_u8(0);
     {
      if (t64) {
       goto zig_block_8;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1313), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_8:;
     zig_usize const t65 = t62.f0;
     zig_L_u8 const t66 = (*t60);
     zig_usize const t67 = t66.len;
     zig_bool const t68 = t65 < t67;
     {
      if (t68) {
       goto zig_block_9;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_9:;
     zig_u8 * const t69 = &t66.ptr[t65];
     zig_u64 const t70 = t12;
     zig_u8 const t71 = (zig_u8 )t70;
     (*t69) = t71;
     /* file:11:13 */
     zig_u64 const t72 = t12;
     zig_u64 const t73 = zig_shr_u64(t72, zig_as_u8(8));
     t12 = t73;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t74;
     t74 = a1;
     zig_L_u8 const * const t75 = (zig_L_u8 const * )&t74;
     zig_usize const t76 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t77;
     t77.f1 = zig_addo_u32(&t77.f0, t76, zig_as_u32(4), zig_as_u8(32));
     zig_u8 const t78 = t77.f1;
     zig_bool const t79 = t78 == zig_as_u8(0);
     {
      if (t79) {
       goto zig_block_10;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1314), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_10:;
     zig_usize const t80 = t77.f0;
     zig_L_u8 const t81 = (*t75);
     zig_usize const t82 = t81.len;
     zig_bool const t83 = t80 < t82;
     {
      if (t83) {
       goto zig_block_11;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_11:;
     zig_u8 * const t84 = &t81.ptr[t80];
     zig_u64 const t85 = t12;
     zig_u8 const t86 = (zig_u8 )t85;
     (*t84) = t86;
     /* file:11:13 */
     zig_u64 const t87 = t12;
     zig_u64 const t88 = zig_shr_u64(t87, zig_as_u8(8));
     t12 = t88;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t89;
     t89 = a1;
     zig_L_u8 const * const t90 = (zig_L_u8 const * )&t89;
     zig_usize const t91 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t92;
     t92.f1 = zig_addo_u32(&t92.f0, t91, zig_as_u32(5), zig_as_u8(32));
     zig_u8 const t93 = t92.f1;
     zig_bool const t94 = t93 == zig_as_u8(0);
     {
      if (t94) {
       goto zig_block_12;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1315), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_12:;
     zig_usize const t95 = t92.f0;
     zig_L_u8 const t96 = (*t90);
     zig_usize const t97 = t96.len;
     zig_bool const t98 = t95 < t97;
     {
      if (t98) {
       goto zig_block_13;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_13:;
     zig_u8 * const t99 = &t96.ptr[t95];
     zig_u64 const t100 = t12;
     zig_u8 const t101 = (zig_u8 )t100;
     (*t99) = t101;
     /* file:11:13 */
     zig_u64 const t102 = t12;
     zig_u64 const t103 = zig_shr_u64(t102, zig_as_u8(8));
     t12 = t103;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t104;
     t104 = a1;
     zig_L_u8 const * const t105 = (zig_L_u8 const * )&t104;
     zig_usize const t106 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t107;
     t107.f1 = zig_addo_u32(&t107.f0, t106, zig_as_u32(6), zig_as_u8(32));
     zig_u8 const t108 = t107.f1;
     zig_bool const t109 = t108 == zig_as_u8(0);
     {
      if (t109) {
       goto zig_block_14;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1316), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_14:;
     zig_usize const t110 = t107.f0;
     zig_L_u8 const t111 = (*t105);
     zig_usize const t112 = t111.len;
     zig_bool const t113 = t110 < t112;
     {
      if (t113) {
       goto zig_block_15;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_15:;
     zig_u8 * const t114 = &t111.ptr[t110];
     zig_u64 const t115 = t12;
     zig_u8 const t116 = (zig_u8 )t115;
     (*t114) = t116;
     /* file:11:13 */
     zig_u64 const t117 = t12;
     zig_u64 const t118 = zig_shr_u64(t117, zig_as_u8(8));
     t12 = t118;
     /* file:9:33 */
     /* file:9:23 */
     /* file:9:41 */
     /* file:10:13 */
     zig_L_u8 t119;
     t119 = a1;
     zig_L_u8 const * const t120 = (zig_L_u8 const * )&t119;
     zig_usize const t121 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t122;
     t122.f1 = zig_addo_u32(&t122.f0, t121, zig_as_u32(7), zig_as_u8(32));
     zig_u8 const t123 = t122.f1;
     zig_bool const t124 = t123 == zig_as_u8(0);
     {
      if (t124) {
       goto zig_block_16;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1317), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_16:;
     zig_usize const t125 = t122.f0;
     zig_L_u8 const t126 = (*t120);
     zig_usize const t127 = t126.len;
     zig_bool const t128 = t125 < t127;
     {
      if (t128) {
       goto zig_block_17;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_17:;
     zig_u8 * const t129 = &t126.ptr[t125];
     zig_u64 const t130 = t12;
     zig_u8 const t131 = (zig_u8 )t130;
     (*t129) = t131;
     /* file:11:13 */
     zig_u64 const t132 = t12;
     zig_u64 const t133 = zig_shr_u64(t132, zig_as_u8(8));
     t12 = t133;
     /* file:9:33 */
     /* file:9:23 */
     /* file:6:32 */
     zig_usize const t134 = t0;
     zig_T_tuple_7busize_2c_20u1_7d t135;
     t135.f1 = zig_addo_u32(&t135.f0, t134, zig_as_u32(8), zig_as_u8(32));
     zig_u8 const t136 = t135.f1;
     zig_bool const t137 = t136 == zig_as_u8(0);
     {
      if (t137) {
       goto zig_block_18;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1318), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_18:;
     zig_usize const t138 = t135.f0;
     t0 = t138;
     goto zig_block_2;
    } else {
     goto zig_block_1;
    }
   }
   zig_block_2:;
  }
 }
 zig_block_1:;
 /* file:16:9 */
 {
  zig_usize const t139 = t0;
  zig_usize const t140 = a1.len;
  zig_u32 t141;
  memcpy(&t141, &t139, sizeof(zig_u32 ));
  t141 = zig_wrap_u32(t141, zig_as_u8(32));
  zig_u32 t142;
  memcpy(&t142, &t140, sizeof(zig_u32 ));
  t142 = zig_wrap_u32(t142, zig_as_u8(32));
  zig_bool const t143 = t141 != t142;
  if (t143) {
   /* file:17:9 */
   zig_u64 t144;
   zig_S_rand_Xoshiro256__255 * t145;
   t145 = a0;
   zig_S_rand_Xoshiro256__255 * const * const t146 = (zig_S_rand_Xoshiro256__255 * const * )&t145;
   zig_S_rand_Xoshiro256__255 * const t147 = (*t146);
   /* file:17:26 */
   zig_u64 const t148 = rand_Xoshiro256_next(t147);
   zig_u64 * const t149 = (zig_u64 * )&t144;
   (*t149) = t148;
   /* var:n */
   {
    while (zig_true) {
     {
      /* file:18:16 */
      zig_usize const t150 = t0;
      zig_usize const t151 = a1.len;
      zig_u32 t152;
      memcpy(&t152, &t150, sizeof(zig_u32 ));
      t152 = zig_wrap_u32(t152, zig_as_u8(32));
      zig_u32 t153;
      memcpy(&t153, &t151, sizeof(zig_u32 ));
      t153 = zig_wrap_u32(t153, zig_as_u8(32));
      zig_bool const t154 = t152 < t153;
      if (t154) {
       /* file:18:40 */
       /* file:19:13 */
       zig_L_u8 t155;
       t155 = a1;
       zig_L_u8 const * const t156 = (zig_L_u8 const * )&t155;
       zig_usize const t157 = t0;
       zig_L_u8 const t158 = (*t156);
       zig_usize const t159 = t158.len;
       zig_bool const t160 = t157 < t159;
       {
        if (t160) {
         goto zig_block_22;
        } else {
         zig_breakpoint();
         zig_unreachable();
        }
       }
       zig_block_22:;
       zig_u8 * const t161 = &t158.ptr[t157];
       zig_u64 const t162 = t144;
       zig_u8 const t163 = (zig_u8 )t162;
       (*t161) = t163;
       /* file:20:13 */
       zig_u64 const t164 = t144;
       zig_u64 const t165 = zig_shr_u64(t164, zig_as_u8(8));
       t144 = t165;
       /* file:18:32 */
       zig_usize const t166 = t0;
       zig_T_tuple_7busize_2c_20u1_7d t167;
       t167.f1 = zig_addo_u32(&t167.f0, t166, zig_as_u32(1), zig_as_u8(32));
       zig_u8 const t168 = t167.f1;
       zig_bool const t169 = t168 == zig_as_u8(0);
       {
        if (t169) {
         goto zig_block_23;
        } else {
         builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Xoshiro256_fill__anon_1319), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
        }
       }
       zig_block_23:;
       zig_usize const t170 = t167.f0;
       t0 = t170;
       goto zig_block_21;
      } else {
       goto zig_block_20;
      }
     }
     zig_block_21:;
    }
   }
   zig_block_20:;
   goto zig_block_19;
  } else {
   goto zig_block_19;
  }
 }
 zig_block_19:;
 return;
}

static zig_S_rand_Random__343 rand_Random_init__anon_747(zig_S_rand_Xoshiro256__255 * const a0) {
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:15 */
 debug_assert(zig_true);
 /* file:4:9 */
 /* file:4:15 */
 debug_assert(zig_true);
 /* file:5:9 */
 /* file:5:15 */
 debug_assert(zig_true);
 /* file:6:9 */
 /* file:14:9 */
 zig_S_rand_Random__343 t0;
 zig_void * * const t1 = (zig_void * * )&t0.ptr;
 zig_usize const t2 = (zig_usize )a0;
 zig_bool const t3 = t2 != zig_as_u32(0);
 {
  if (t3) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Random_init__anon_747__anon_1429), zig_as_u32(30)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_void * const t4 = (zig_void * )a0;
 (*t1) = t4;
 zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void * const t5 = (zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void * )&t0.fillFn;
 (*t5) = (zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void )&rand_Random_init__anon_747_gen_fill;
 /* file:14:9 */
 return t0;
}

static zig_void rand_Random_bytes(zig_S_rand_Random__343 const a0, zig_L_u8 const a1) {
 /* file:2:9 */
 zig_S_rand_Random__343 t0;
 t0 = a0;
 zig_S_rand_Random__343 const * const t1 = (zig_S_rand_Random__343 const * )&t0;
 zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void const * const t2 = (zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void const * )&t1->fillFn;
 zig_F_fn_28_2aanyopaque_2c_20_5b_5du8_29_20void const t3 = (*t2);
 /* file:2:17 */
 zig_void * const t4 = a0.ptr;
 t3(t4, a1);
 return;
}

static zig_S_target_Target_Cpu_Feature_Set__1123 target_Target_Cpu_Feature_feature_set_fns_28target_mips_Feature_29_featureSet(zig_L_target_mips_Feature const a0) {
 /* file:2:25 */
 zig_S_target_Target_Cpu_Feature_Set__1123 t0;
 /* file:2:53 */
 zig_S_target_Target_Cpu_Feature_Set__1123 const t1 = target_Target_Cpu_Feature_Set_empty_workaround();
 zig_S_target_Target_Cpu_Feature_Set__1123 * const t2 = (zig_S_target_Target_Cpu_Feature_Set__1123 * )&t0;
 (*t2) = t1;
 /* var:x */
 /* file:3:30 */
 zig_usize const t3 = a0.len;
 zig_usize t4;
 t4 = zig_as_u32(0);
 {
  while (zig_true) {
   {
    zig_usize const t5 = t4;
    zig_u32 t6;
    memcpy(&t6, &t5, sizeof(zig_u32 ));
    t6 = zig_wrap_u32(t6, zig_as_u8(32));
    zig_u32 t7;
    memcpy(&t7, &t3, sizeof(zig_u32 ));
    t7 = zig_wrap_u32(t7, zig_as_u8(32));
    zig_bool const t8 = t6 < t7;
    if (t8) {
     zig_usize const t9 = a0.len;
     zig_bool const t10 = t5 < t9;
     {
      if (t10) {
       goto zig_block_2;
      } else {
       zig_breakpoint();
       zig_unreachable();
      }
     }
     zig_block_2:;
     zig_u8 const t11 = a0.ptr[t5];
     /* var:feature */
     /* file:4:29 */
     /* file:4:41 */
     zig_u8 t12;
     memcpy(&t12, &t11, sizeof(zig_u8 ));
     t12 = zig_wrap_u8(t12, zig_as_u8(6));
     zig_u16 const t13 = (zig_u16 )t12;
     target_Target_Cpu_Feature_Set_addFeature(&t0, t13);
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
   zig_usize const t14 = t4;
   zig_T_tuple_7busize_2c_20u1_7d t15;
   t15.f1 = zig_addo_u32(&t15.f0, t14, zig_as_u32(1), zig_as_u8(32));
   zig_u8 const t16 = t15.f1;
   zig_bool const t17 = t16 == zig_as_u8(0);
   {
    if (t17) {
     goto zig_block_3;
    } else {
     builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&target_Target_Cpu_Feature_feature_set_fns_28target_mips_Feature_29_featureSet__anon_1430), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
    }
   }
   zig_block_3:;
   zig_usize const t18 = t15.f0;
   t4 = t18;
  }
 }
 zig_block_0:;
 /* file:6:25 */
 zig_S_target_Target_Cpu_Feature_Set__1123 const t19 = t0;
 /* file:6:25 */
 return t19;
}

static zig_S_target_Target_Cpu_Feature_Set__1123 target_Target_Cpu_Feature_Set_empty_workaround(zig_void) {
 /* file:2:21 */
 zig_S_target_Target_Cpu_Feature_Set__1123 t0;
 zig_S_target_Target_Cpu_Feature_Set__1123 * const t1 = (zig_S_target_Target_Cpu_Feature_Set__1123 * )&t0;
 (*t1) = (zig_S_target_Target_Cpu_Feature_Set__1123 ){{zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0)}};
 /* file:2:21 */
 return t0;
}

static zig_void target_Target_Cpu_Feature_Set_addFeature(zig_S_target_Target_Cpu_Feature_Set__1123 * const a0, zig_u16 const a1) {
 /* file:2:21 */
 zig_u16 const t0 = a1 / zig_as_u16(32);
 /* var:usize_index */
 /* file:3:21 */
 zig_u16 const t1 = a1 % zig_as_u16(32);
 zig_u16 const t2 = zig_subw_u16(zig_as_u16(31), t1, zig_as_u8(9));
 zig_bool const t3 = t2 <= zig_as_u16(31);
 {
  if (t3) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&target_Target_Cpu_Feature_Set_addFeature__anon_1431), zig_as_u32(27)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_u8 const t4 = (zig_u8 )t1;
 /* var:bit_index */
 /* file:4:21 */
 zig_S_target_Target_Cpu_Feature_Set__1123 * t5;
 t5 = a0;
 zig_S_target_Target_Cpu_Feature_Set__1123 * const * const t6 = (zig_S_target_Target_Cpu_Feature_Set__1123 * const * )&t5;
 zig_S_target_Target_Cpu_Feature_Set__1123 * const t7 = (*t6);
 zig_A_usize_9 * const t8 = (zig_A_usize_9 * )&t7->ints;
 zig_usize const t9 = (zig_usize )t0;
 zig_bool const t10 = t9 < zig_as_u32(9);
 {
  if (t10) {
   goto zig_block_1;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_1:;
 zig_usize * const t11 = &((*t8))[t9];
 zig_usize const t12 = (*t11);
 zig_usize const t13 = zig_shlw_u32(zig_as_u32(1), t4, zig_as_u8(32));
 zig_usize const t14 = t12 | t13;
 (*t11) = t14;
 return;
}
static zig_S_target_Target_Cpu_Model__1116 target_mips_cpu_mips32 = {{(zig_u8 const * )((zig_u8 const * )&target_mips_cpu_mips32__anon_1172), zig_as_u32(6)},{(zig_u8 const * )((zig_u8 const * )&target_mips_cpu_mips32__anon_1172), zig_as_u32(6)},{{zig_as_u32(262144),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0)}}};
static zig_S_target_Target_Cpu__1087 builtin_cpu = {16,(zig_S_target_Target_Cpu_Model__1116 const * )((zig_S_target_Target_Cpu_Model__1116 const * )&target_mips_cpu_mips32),{{zig_as_u32(142950400),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0),zig_as_u32(0)}}};

static zig_u8 target_Target_Cpu_Arch_endian(zig_u8 const a0) {
 /* file:2:17 */
 zig_u8 t0;
 /* file:2:32 */
 {
  switch (a0) {
   case 6: 
   case 0: 
   case 4: 
   case 2: 
   case 25: 
   case 43: 
   case 44: 
   case 7: 
   case 9: 
   case 11: 
   case 45: 
   case 46: 
   case 51: 
   case 41: 
   case 42: 
   case 16: 
   case 18: 
   case 19: 
   case 39: 
   case 40: 
   case 30: 
   case 33: 
   case 21: 
   case 23: 
   case 24: 
   case 26: 
   case 27: 
   case 36: 
   case 37: 
   case 54: 
   case 55: 
   case 38: 
   case 34: 
   case 47: 
   case 48: 
   case 56: 
   case 57: 
   case 52: 
   case 58: 
   case 59: 
   case 49: 
   case 50: 
   case 10: 
   case 12: 
   case 13: {
    t0 = 1;
    goto zig_block_0;
   }
   case 5: 
   case 1: 
   case 3: 
   case 8: 
   case 14: 
   case 15: 
   case 17: 
   case 20: 
   case 22: 
   case 35: 
   case 28: 
   case 29: 
   case 32: 
   case 53: 
   case 31: {
    t0 = 0;
    goto zig_block_0;
   }
   default: {
    /* file:2:32 */
    builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&target_Target_Cpu_Arch_endian__anon_1432), zig_as_u32(23)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
   }
  }
 }
 zig_block_0:;
 /* file:2:17 */
 return t0;
}
static zig_u8 mem_native_endian = 1;

static zig_u32 mem_readIntSliceNative__anon_1200(zig_L_u8 const a0) {
 /* file:2:5 */
 /* file:3:5 */
 /* file:3:11 */
 zig_usize const t0 = a0.len;
 zig_u32 t1;
 memcpy(&t1, &t0, sizeof(zig_u32 ));
 t1 = zig_wrap_u32(t1, zig_as_u8(32));
 zig_bool const t2 = t1 >= zig_as_u32(4);
 debug_assert(t2);
 /* file:4:5 */
 zig_u32 t3;
 /* file:4:25 */
 zig_L_u8 t4;
 t4 = a0;
 zig_L_u8 const * const t5 = (zig_L_u8 const * )&t4;
 zig_L_u8 const t6 = (*t5);
 zig_u8 const * const t7 = t6.ptr;
 zig_u8 const * const t8 = (zig_u8 const * )(((uintptr_t)t7) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_4 const * const t9 = (zig_A_u8_4 const * )t8;
 zig_usize const t10 = t6.len;
 zig_bool const t11 = zig_as_u32(4) <= t10;
 {
  if (t11) {
   goto zig_block_0;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_0:;
 zig_u32 const t12 = mem_readIntNative__anon_1433(t9);
 t3 = t12;
 /* file:4:5 */
 return t3;
}

static zig_u64 rand_Random_int__anon_1201(zig_S_rand_Random__343 const a0) {
 static zig_u8 const t1[zig_as_u32(8)] = {zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa), zig_as_u8(0xaa)};
 /* file:2:9 */
 /* file:3:9 */
 /* file:3:39 */
 /* file:4:9 */
 /* file:4:42 */
 /* file:6:9 */
 zig_u8 t0[zig_as_u32(8)];
 memset(&t0, zig_as_u8(0xaa), sizeof(zig_u8 [zig_as_u32(8)]));
 /* var:rand_bytes */
 /* file:7:9 */
 zig_S_rand_Random__343 t2;
 t2 = a0;
 zig_S_rand_Random__343 const * const t3 = (zig_S_rand_Random__343 const * )&t2;
 zig_S_rand_Random__343 const t4 = (*t3);
 /* file:7:16 */
 zig_A_u8_8 * const t5 = (zig_A_u8_8 * )(((uintptr_t)&t0) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_8 * const t6 = (zig_A_u8_8 * )t5;
 zig_L_u8 const t7 = { .ptr = &((*t6))[zig_as_u32(0)], .len = zig_as_u32(8) };
 rand_Random_bytes(t4, t7);
 /* file:12:9 */
 /* file:12:59 */
 zig_L_u8 const t8 = { .ptr = &(t0)[zig_as_u32(0)], .len = zig_as_u32(8) };
 zig_u64 const t9 = mem_readIntSliceNative__anon_1434(t8);
 /* var:byte_aligned_result */
 /* file:13:9 */
 zig_u64 const t10 = (zig_u64 )t9;
 /* var:unsigned_result */
 /* file:14:9 */
 zig_u64 t11;
 memcpy(&t11, &t10, sizeof(zig_u64 ));
 t11 = zig_wrap_u64(t11, zig_as_u8(64));
 /* file:14:9 */
 return t11;
}

static zig_u8 mem_readIntSliceNative__anon_1228(zig_L_u8 const a0) {
 /* file:2:5 */
 /* file:3:5 */
 /* file:3:11 */
 zig_usize const t0 = a0.len;
 zig_u32 t1;
 memcpy(&t1, &t0, sizeof(zig_u32 ));
 t1 = zig_wrap_u32(t1, zig_as_u8(32));
 zig_bool const t2 = t1 >= zig_as_u32(1);
 debug_assert(t2);
 /* file:4:5 */
 zig_u8 t3;
 /* file:4:25 */
 zig_L_u8 t4;
 t4 = a0;
 zig_L_u8 const * const t5 = (zig_L_u8 const * )&t4;
 zig_L_u8 const t6 = (*t5);
 zig_u8 const * const t7 = t6.ptr;
 zig_u8 const * const t8 = (zig_u8 const * )(((uintptr_t)t7) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_1 const * const t9 = (zig_A_u8_1 const * )t8;
 zig_usize const t10 = t6.len;
 zig_bool const t11 = zig_as_u32(1) <= t10;
 {
  if (t11) {
   goto zig_block_0;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_0:;
 zig_u8 const t12 = mem_readIntNative__anon_1435(t9);
 t3 = t12;
 /* file:4:5 */
 return t3;
}

static zig_bool generator_isSpaceForTree(zig_u32 const a0, zig_u32 const a1, zig_u32 const a2) {
 /* file:2:5 */
 zig_u32 t0;
 t0 = zig_as_u32(0);
 /* var:i */
 {
  while (zig_true) {
   {
    /* file:3:11 */
    zig_u32 const t1 = t0;
    zig_bool const t2 = t1 < zig_as_u32(6);
    if (t2) {
     /* file:3:29 */
     /* file:4:9 */
     zig_u32 t3;
     zig_T_tuple_7bu32_2c_20u1_7d t4;
     t4.f1 = zig_subo_u32(&t4.f0, a0, zig_as_u32(2), zig_as_u8(32));
     zig_u8 const t5 = t4.f1;
     zig_bool const t6 = t5 == zig_as_u8(0);
     {
      if (t6) {
       goto zig_block_2;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1436), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_2:;
     zig_u32 const t7 = t4.f0;
     zig_u32 * const t8 = (zig_u32 * )&t3;
     (*t8) = t7;
     /* var:cx */
     {
      while (zig_true) {
       {
        /* file:5:15 */
        zig_u32 const t9 = t3;
        zig_T_tuple_7bu32_2c_20u1_7d t10;
        t10.f1 = zig_addo_u32(&t10.f0, a0, zig_as_u32(2), zig_as_u8(32));
        zig_u8 const t11 = t10.f1;
        zig_bool const t12 = t11 == zig_as_u8(0);
        {
         if (t12) {
          goto zig_block_5;
         } else {
          builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1437), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
         }
        }
        zig_block_5:;
        zig_u32 const t13 = t10.f0;
        zig_bool const t14 = t9 <= t13;
        if (t14) {
         /* file:5:40 */
         /* file:6:13 */
         zig_u32 t15;
         zig_T_tuple_7bu32_2c_20u1_7d t16;
         t16.f1 = zig_subo_u32(&t16.f0, a2, zig_as_u32(2), zig_as_u8(32));
         zig_u8 const t17 = t16.f1;
         zig_bool const t18 = t17 == zig_as_u8(0);
         {
          if (t18) {
           goto zig_block_6;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1438), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_6:;
         zig_u32 const t19 = t16.f0;
         zig_u32 * const t20 = (zig_u32 * )&t15;
         (*t20) = t19;
         /* var:cz */
         {
          while (zig_true) {
           {
            /* file:7:19 */
            zig_u32 const t21 = t15;
            zig_T_tuple_7bu32_2c_20u1_7d t22;
            t22.f1 = zig_addo_u32(&t22.f0, a2, zig_as_u32(2), zig_as_u8(32));
            zig_u8 const t23 = t22.f1;
            zig_bool const t24 = t23 == zig_as_u8(0);
            {
             if (t24) {
              goto zig_block_9;
             } else {
              builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1439), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
             }
            }
            zig_block_9:;
            zig_u32 const t25 = t22.f0;
            zig_bool const t26 = t21 <= t25;
            if (t26) {
             /* file:7:44 */
             /* file:8:17 */
             zig_usize t27;
             /* file:8:33 */
             zig_u32 const t28 = t3;
             zig_u32 const t29 = t0;
             zig_T_tuple_7bu32_2c_20u1_7d t30;
             t30.f1 = zig_addo_u32(&t30.f0, a1, t29, zig_as_u8(32));
             zig_u8 const t31 = t30.f1;
             zig_bool const t32 = t31 == zig_as_u8(0);
             {
              if (t32) {
               goto zig_block_10;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1440), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_10:;
             zig_u32 const t33 = t30.f0;
             zig_u32 const t34 = t15;
             zig_usize const t35 = generator_getIdx(t28, t33, t34);
             zig_usize * const t36 = (zig_usize * )&t27;
             (*t36) = t35;
             /* var:idx */
             /* file:9:17 */
             zig_u8 t37;
             zig_u8 * const t38 = (*(zig_u8 * * )((zig_u8 * * )&generator_worldData));
             zig_usize const t39 = t27;
             zig_u8 const t40 = t38[t39];
             zig_u8 * const t41 = (zig_u8 * )&t37;
             (*t41) = t40;
             /* var:blk */
             /* file:11:20 */
             {
              zig_u8 const t42 = t37;
              zig_bool const t43 = t42 != zig_as_u8(0);
              if (t43) {
               /* file:12:21 */
               /* file:12:21 */
               return zig_false;
              } else {
               goto zig_block_11;
              }
             }
             zig_block_11:;
             /* file:7:35 */
             zig_u32 const t44 = t15;
             zig_T_tuple_7bu32_2c_20u1_7d t45;
             t45.f1 = zig_addo_u32(&t45.f0, t44, zig_as_u32(1), zig_as_u8(32));
             zig_u8 const t46 = t45.f1;
             zig_bool const t47 = t46 == zig_as_u8(0);
             {
              if (t47) {
               goto zig_block_12;
              } else {
               builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1441), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
              }
             }
             zig_block_12:;
             zig_u32 const t48 = t45.f0;
             t15 = t48;
             goto zig_block_8;
            } else {
             goto zig_block_7;
            }
           }
           zig_block_8:;
          }
         }
         zig_block_7:;
         /* file:5:31 */
         zig_u32 const t49 = t3;
         zig_T_tuple_7bu32_2c_20u1_7d t50;
         t50.f1 = zig_addo_u32(&t50.f0, t49, zig_as_u32(1), zig_as_u8(32));
         zig_u8 const t51 = t50.f1;
         zig_bool const t52 = t51 == zig_as_u8(0);
         {
          if (t52) {
           goto zig_block_13;
          } else {
           builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1442), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
          }
         }
         zig_block_13:;
         zig_u32 const t53 = t50.f0;
         t3 = t53;
         goto zig_block_4;
        } else {
         goto zig_block_3;
        }
       }
       zig_block_4:;
      }
     }
     zig_block_3:;
     /* file:3:21 */
     zig_u32 const t54 = t0;
     zig_T_tuple_7bu32_2c_20u1_7d t55;
     t55.f1 = zig_addo_u32(&t55.f0, t54, zig_as_u32(1), zig_as_u8(32));
     zig_u8 const t56 = t55.f1;
     zig_bool const t57 = t56 == zig_as_u8(0);
     {
      if (t57) {
       goto zig_block_14;
      } else {
       builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&generator_isSpaceForTree__anon_1443), zig_as_u32(16)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
      }
     }
     zig_block_14:;
     zig_u32 const t58 = t55.f0;
     t0 = t58;
     goto zig_block_1;
    } else {
     goto zig_block_0;
    }
   }
   zig_block_1:;
  }
 }
 zig_block_0:;
 /* file:17:5 */
 /* file:17:5 */
 return zig_true;
}

static zig_f64 perlin_fade(zig_f64 const a0) {
 /* file:2:5 */
 zig_f64 const t0 = zig_mul_f64(a0, a0);
 zig_f64 const t1 = zig_mul_f64(t0, a0);
 zig_f64 const t2 = zig_mul_f64(a0, (zig_f64 )zig_as_f64(0x1.8p2, zig_as_i64(0x4018000000000000)));
 zig_f64 const t3 = zig_sub_f64(t2, (zig_f64 )zig_as_f64(0x1.ep3, zig_as_i64(0x402e000000000000)));
 zig_f64 const t4 = zig_mul_f64(a0, t3);
 zig_f64 const t5 = zig_add_f64(t4, (zig_f64 )zig_as_f64(0x1.4p3, zig_as_i64(0x4024000000000000)));
 zig_f64 const t6 = zig_mul_f64(t1, t5);
 /* file:2:5 */
 return t6;
}
static zig_usize perlin_permutation[zig_as_u32(512)] = {zig_as_u32(151),zig_as_u32(160),zig_as_u32(137),zig_as_u32(91),zig_as_u32(90),zig_as_u32(15),zig_as_u32(131),zig_as_u32(13),zig_as_u32(201),zig_as_u32(95),zig_as_u32(96),zig_as_u32(53),zig_as_u32(194),zig_as_u32(233),zig_as_u32(7),zig_as_u32(225),zig_as_u32(140),zig_as_u32(36),zig_as_u32(103),zig_as_u32(30),zig_as_u32(69),zig_as_u32(142),zig_as_u32(8),zig_as_u32(99),zig_as_u32(37),zig_as_u32(240),zig_as_u32(21),zig_as_u32(10),zig_as_u32(23),zig_as_u32(190),zig_as_u32(6),zig_as_u32(148),zig_as_u32(247),zig_as_u32(120),zig_as_u32(234),zig_as_u32(75),zig_as_u32(0),zig_as_u32(26),zig_as_u32(197),zig_as_u32(62),zig_as_u32(94),zig_as_u32(252),zig_as_u32(219),zig_as_u32(203),zig_as_u32(117),zig_as_u32(35),zig_as_u32(11),zig_as_u32(32),zig_as_u32(57),zig_as_u32(177),zig_as_u32(33),zig_as_u32(88),zig_as_u32(237),zig_as_u32(149),zig_as_u32(56),zig_as_u32(87),zig_as_u32(174),zig_as_u32(20),zig_as_u32(125),zig_as_u32(136),zig_as_u32(171),zig_as_u32(168),zig_as_u32(68),zig_as_u32(175),zig_as_u32(74),zig_as_u32(165),zig_as_u32(71),zig_as_u32(134),zig_as_u32(139),zig_as_u32(48),zig_as_u32(27),zig_as_u32(166),zig_as_u32(77),zig_as_u32(146),zig_as_u32(158),zig_as_u32(231),zig_as_u32(83),zig_as_u32(111),zig_as_u32(229),zig_as_u32(122),zig_as_u32(60),zig_as_u32(211),zig_as_u32(133),zig_as_u32(230),zig_as_u32(220),zig_as_u32(105),zig_as_u32(92),zig_as_u32(41),zig_as_u32(55),zig_as_u32(46),zig_as_u32(245),zig_as_u32(40),zig_as_u32(244),zig_as_u32(102),zig_as_u32(143),zig_as_u32(54),zig_as_u32(65),zig_as_u32(25),zig_as_u32(63),zig_as_u32(161),zig_as_u32(1),zig_as_u32(216),zig_as_u32(80),zig_as_u32(73),zig_as_u32(209),zig_as_u32(76),zig_as_u32(132),zig_as_u32(187),zig_as_u32(208),zig_as_u32(89),zig_as_u32(18),zig_as_u32(169),zig_as_u32(200),zig_as_u32(196),zig_as_u32(135),zig_as_u32(130),zig_as_u32(116),zig_as_u32(188),zig_as_u32(159),zig_as_u32(86),zig_as_u32(164),zig_as_u32(100),zig_as_u32(109),zig_as_u32(198),zig_as_u32(173),zig_as_u32(186),zig_as_u32(3),zig_as_u32(64),zig_as_u32(52),zig_as_u32(217),zig_as_u32(226),zig_as_u32(250),zig_as_u32(124),zig_as_u32(123),zig_as_u32(5),zig_as_u32(202),zig_as_u32(38),zig_as_u32(147),zig_as_u32(118),zig_as_u32(126),zig_as_u32(255),zig_as_u32(82),zig_as_u32(85),zig_as_u32(212),zig_as_u32(207),zig_as_u32(206),zig_as_u32(59),zig_as_u32(227),zig_as_u32(47),zig_as_u32(16),zig_as_u32(58),zig_as_u32(17),zig_as_u32(182),zig_as_u32(189),zig_as_u32(28),zig_as_u32(42),zig_as_u32(223),zig_as_u32(183),zig_as_u32(170),zig_as_u32(213),zig_as_u32(119),zig_as_u32(248),zig_as_u32(152),zig_as_u32(2),zig_as_u32(44),zig_as_u32(154),zig_as_u32(163),zig_as_u32(70),zig_as_u32(221),zig_as_u32(153),zig_as_u32(101),zig_as_u32(155),zig_as_u32(167),zig_as_u32(43),zig_as_u32(172),zig_as_u32(9),zig_as_u32(129),zig_as_u32(22),zig_as_u32(39),zig_as_u32(253),zig_as_u32(19),zig_as_u32(98),zig_as_u32(108),zig_as_u32(110),zig_as_u32(79),zig_as_u32(113),zig_as_u32(224),zig_as_u32(232),zig_as_u32(178),zig_as_u32(185),zig_as_u32(112),zig_as_u32(104),zig_as_u32(218),zig_as_u32(246),zig_as_u32(97),zig_as_u32(228),zig_as_u32(251),zig_as_u32(34),zig_as_u32(242),zig_as_u32(193),zig_as_u32(238),zig_as_u32(210),zig_as_u32(144),zig_as_u32(12),zig_as_u32(191),zig_as_u32(179),zig_as_u32(162),zig_as_u32(241),zig_as_u32(81),zig_as_u32(51),zig_as_u32(145),zig_as_u32(235),zig_as_u32(249),zig_as_u32(14),zig_as_u32(239),zig_as_u32(107),zig_as_u32(49),zig_as_u32(192),zig_as_u32(214),zig_as_u32(31),zig_as_u32(181),zig_as_u32(199),zig_as_u32(106),zig_as_u32(157),zig_as_u32(184),zig_as_u32(84),zig_as_u32(204),zig_as_u32(176),zig_as_u32(115),zig_as_u32(121),zig_as_u32(50),zig_as_u32(45),zig_as_u32(127),zig_as_u32(4),zig_as_u32(150),zig_as_u32(254),zig_as_u32(138),zig_as_u32(236),zig_as_u32(205),zig_as_u32(93),zig_as_u32(222),zig_as_u32(114),zig_as_u32(67),zig_as_u32(29),zig_as_u32(24),zig_as_u32(72),zig_as_u32(243),zig_as_u32(141),zig_as_u32(128),zig_as_u32(195),zig_as_u32(78),zig_as_u32(66),zig_as_u32(215),zig_as_u32(61),zig_as_u32(156),zig_as_u32(180),zig_as_u32(151),zig_as_u32(160),zig_as_u32(137),zig_as_u32(91),zig_as_u32(90),zig_as_u32(15),zig_as_u32(131),zig_as_u32(13),zig_as_u32(201),zig_as_u32(95),zig_as_u32(96),zig_as_u32(53),zig_as_u32(194),zig_as_u32(233),zig_as_u32(7),zig_as_u32(225),zig_as_u32(140),zig_as_u32(36),zig_as_u32(103),zig_as_u32(30),zig_as_u32(69),zig_as_u32(142),zig_as_u32(8),zig_as_u32(99),zig_as_u32(37),zig_as_u32(240),zig_as_u32(21),zig_as_u32(10),zig_as_u32(23),zig_as_u32(190),zig_as_u32(6),zig_as_u32(148),zig_as_u32(247),zig_as_u32(120),zig_as_u32(234),zig_as_u32(75),zig_as_u32(0),zig_as_u32(26),zig_as_u32(197),zig_as_u32(62),zig_as_u32(94),zig_as_u32(252),zig_as_u32(219),zig_as_u32(203),zig_as_u32(117),zig_as_u32(35),zig_as_u32(11),zig_as_u32(32),zig_as_u32(57),zig_as_u32(177),zig_as_u32(33),zig_as_u32(88),zig_as_u32(237),zig_as_u32(149),zig_as_u32(56),zig_as_u32(87),zig_as_u32(174),zig_as_u32(20),zig_as_u32(125),zig_as_u32(136),zig_as_u32(171),zig_as_u32(168),zig_as_u32(68),zig_as_u32(175),zig_as_u32(74),zig_as_u32(165),zig_as_u32(71),zig_as_u32(134),zig_as_u32(139),zig_as_u32(48),zig_as_u32(27),zig_as_u32(166),zig_as_u32(77),zig_as_u32(146),zig_as_u32(158),zig_as_u32(231),zig_as_u32(83),zig_as_u32(111),zig_as_u32(229),zig_as_u32(122),zig_as_u32(60),zig_as_u32(211),zig_as_u32(133),zig_as_u32(230),zig_as_u32(220),zig_as_u32(105),zig_as_u32(92),zig_as_u32(41),zig_as_u32(55),zig_as_u32(46),zig_as_u32(245),zig_as_u32(40),zig_as_u32(244),zig_as_u32(102),zig_as_u32(143),zig_as_u32(54),zig_as_u32(65),zig_as_u32(25),zig_as_u32(63),zig_as_u32(161),zig_as_u32(1),zig_as_u32(216),zig_as_u32(80),zig_as_u32(73),zig_as_u32(209),zig_as_u32(76),zig_as_u32(132),zig_as_u32(187),zig_as_u32(208),zig_as_u32(89),zig_as_u32(18),zig_as_u32(169),zig_as_u32(200),zig_as_u32(196),zig_as_u32(135),zig_as_u32(130),zig_as_u32(116),zig_as_u32(188),zig_as_u32(159),zig_as_u32(86),zig_as_u32(164),zig_as_u32(100),zig_as_u32(109),zig_as_u32(198),zig_as_u32(173),zig_as_u32(186),zig_as_u32(3),zig_as_u32(64),zig_as_u32(52),zig_as_u32(217),zig_as_u32(226),zig_as_u32(250),zig_as_u32(124),zig_as_u32(123),zig_as_u32(5),zig_as_u32(202),zig_as_u32(38),zig_as_u32(147),zig_as_u32(118),zig_as_u32(126),zig_as_u32(255),zig_as_u32(82),zig_as_u32(85),zig_as_u32(212),zig_as_u32(207),zig_as_u32(206),zig_as_u32(59),zig_as_u32(227),zig_as_u32(47),zig_as_u32(16),zig_as_u32(58),zig_as_u32(17),zig_as_u32(182),zig_as_u32(189),zig_as_u32(28),zig_as_u32(42),zig_as_u32(223),zig_as_u32(183),zig_as_u32(170),zig_as_u32(213),zig_as_u32(119),zig_as_u32(248),zig_as_u32(152),zig_as_u32(2),zig_as_u32(44),zig_as_u32(154),zig_as_u32(163),zig_as_u32(70),zig_as_u32(221),zig_as_u32(153),zig_as_u32(101),zig_as_u32(155),zig_as_u32(167),zig_as_u32(43),zig_as_u32(172),zig_as_u32(9),zig_as_u32(129),zig_as_u32(22),zig_as_u32(39),zig_as_u32(253),zig_as_u32(19),zig_as_u32(98),zig_as_u32(108),zig_as_u32(110),zig_as_u32(79),zig_as_u32(113),zig_as_u32(224),zig_as_u32(232),zig_as_u32(178),zig_as_u32(185),zig_as_u32(112),zig_as_u32(104),zig_as_u32(218),zig_as_u32(246),zig_as_u32(97),zig_as_u32(228),zig_as_u32(251),zig_as_u32(34),zig_as_u32(242),zig_as_u32(193),zig_as_u32(238),zig_as_u32(210),zig_as_u32(144),zig_as_u32(12),zig_as_u32(191),zig_as_u32(179),zig_as_u32(162),zig_as_u32(241),zig_as_u32(81),zig_as_u32(51),zig_as_u32(145),zig_as_u32(235),zig_as_u32(249),zig_as_u32(14),zig_as_u32(239),zig_as_u32(107),zig_as_u32(49),zig_as_u32(192),zig_as_u32(214),zig_as_u32(31),zig_as_u32(181),zig_as_u32(199),zig_as_u32(106),zig_as_u32(157),zig_as_u32(184),zig_as_u32(84),zig_as_u32(204),zig_as_u32(176),zig_as_u32(115),zig_as_u32(121),zig_as_u32(50),zig_as_u32(45),zig_as_u32(127),zig_as_u32(4),zig_as_u32(150),zig_as_u32(254),zig_as_u32(138),zig_as_u32(236),zig_as_u32(205),zig_as_u32(93),zig_as_u32(222),zig_as_u32(114),zig_as_u32(67),zig_as_u32(29),zig_as_u32(24),zig_as_u32(72),zig_as_u32(243),zig_as_u32(141),zig_as_u32(128),zig_as_u32(195),zig_as_u32(78),zig_as_u32(66),zig_as_u32(215),zig_as_u32(61),zig_as_u32(156),zig_as_u32(180)};

static zig_f64 perlin_lerp(zig_f64 const a0, zig_f64 const a1, zig_f64 const a2) {
 /* file:2:5 */
 zig_f64 const t0 = zig_sub_f64(a2, a1);
 zig_f64 const t1 = zig_mul_f64(a0, t0);
 zig_f64 const t2 = zig_add_f64(a1, t1);
 /* file:2:5 */
 return t2;
}

static zig_u64 rand_Xoshiro256_next(zig_S_rand_Xoshiro256__255 * const a0) {
 /* file:2:5 */
 /* file:2:24 */
 zig_A_u64_4 * const t0 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t1[zig_as_u32(4)];
 memcpy(t1, t0, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t2 = t1[zig_as_u32(0)];
 zig_A_u64_4 * const t3 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t4[zig_as_u32(4)];
 memcpy(t4, t3, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t5 = t4[zig_as_u32(3)];
 zig_u64 const t6 = zig_addw_u64(t2, t5, zig_as_u8(64));
 zig_u64 const t7 = math_rotl__anon_1444(t6);
 zig_A_u64_4 * const t8 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t9[zig_as_u32(4)];
 memcpy(t9, t8, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t10 = t9[zig_as_u32(0)];
 zig_u64 const t11 = zig_addw_u64(t7, t10, zig_as_u8(64));
 /* var:r */
 /* file:4:5 */
 zig_A_u64_4 * const t12 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t13[zig_as_u32(4)];
 memcpy(t13, t12, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t14 = t13[zig_as_u32(1)];
 zig_u64 const t15 = zig_shlw_u64(t14, zig_as_u8(17), zig_as_u8(64));
 /* var:t */
 /* file:6:5 */
 zig_S_rand_Xoshiro256__255 * t16;
 t16 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t17 = (zig_S_rand_Xoshiro256__255 * const * )&t16;
 zig_S_rand_Xoshiro256__255 * const t18 = (*t17);
 zig_A_u64_4 * const t19 = (zig_A_u64_4 * )&t18->s;
 zig_u64 * const t20 = &((*t19))[zig_as_u32(2)];
 zig_u64 const t21 = (*t20);
 zig_A_u64_4 * const t22 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t23[zig_as_u32(4)];
 memcpy(t23, t22, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t24 = t23[zig_as_u32(0)];
 zig_u64 const t25 = t21 ^ t24;
 (*t20) = t25;
 /* file:7:5 */
 zig_S_rand_Xoshiro256__255 * t26;
 t26 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t27 = (zig_S_rand_Xoshiro256__255 * const * )&t26;
 zig_S_rand_Xoshiro256__255 * const t28 = (*t27);
 zig_A_u64_4 * const t29 = (zig_A_u64_4 * )&t28->s;
 zig_u64 * const t30 = &((*t29))[zig_as_u32(3)];
 zig_u64 const t31 = (*t30);
 zig_A_u64_4 * const t32 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t33[zig_as_u32(4)];
 memcpy(t33, t32, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t34 = t33[zig_as_u32(1)];
 zig_u64 const t35 = t31 ^ t34;
 (*t30) = t35;
 /* file:8:5 */
 zig_S_rand_Xoshiro256__255 * t36;
 t36 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t37 = (zig_S_rand_Xoshiro256__255 * const * )&t36;
 zig_S_rand_Xoshiro256__255 * const t38 = (*t37);
 zig_A_u64_4 * const t39 = (zig_A_u64_4 * )&t38->s;
 zig_u64 * const t40 = &((*t39))[zig_as_u32(1)];
 zig_u64 const t41 = (*t40);
 zig_A_u64_4 * const t42 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t43[zig_as_u32(4)];
 memcpy(t43, t42, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t44 = t43[zig_as_u32(2)];
 zig_u64 const t45 = t41 ^ t44;
 (*t40) = t45;
 /* file:9:5 */
 zig_S_rand_Xoshiro256__255 * t46;
 t46 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t47 = (zig_S_rand_Xoshiro256__255 * const * )&t46;
 zig_S_rand_Xoshiro256__255 * const t48 = (*t47);
 zig_A_u64_4 * const t49 = (zig_A_u64_4 * )&t48->s;
 zig_u64 * const t50 = &((*t49))[zig_as_u32(0)];
 zig_u64 const t51 = (*t50);
 zig_A_u64_4 * const t52 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t53[zig_as_u32(4)];
 memcpy(t53, t52, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t54 = t53[zig_as_u32(3)];
 zig_u64 const t55 = t51 ^ t54;
 (*t50) = t55;
 /* file:11:5 */
 zig_S_rand_Xoshiro256__255 * t56;
 t56 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t57 = (zig_S_rand_Xoshiro256__255 * const * )&t56;
 zig_S_rand_Xoshiro256__255 * const t58 = (*t57);
 zig_A_u64_4 * const t59 = (zig_A_u64_4 * )&t58->s;
 zig_u64 * const t60 = &((*t59))[zig_as_u32(2)];
 zig_u64 const t61 = (*t60);
 zig_u64 const t62 = t61 ^ t15;
 (*t60) = t62;
 /* file:13:5 */
 zig_S_rand_Xoshiro256__255 * t63;
 t63 = a0;
 zig_S_rand_Xoshiro256__255 * const * const t64 = (zig_S_rand_Xoshiro256__255 * const * )&t63;
 zig_S_rand_Xoshiro256__255 * const t65 = (*t64);
 zig_A_u64_4 * const t66 = (zig_A_u64_4 * )&t65->s;
 zig_u64 * const t67 = &((*t66))[zig_as_u32(3)];
 /* file:13:26 */
 zig_A_u64_4 * const t68 = (zig_A_u64_4 * )&a0->s;
 zig_u64 t69[zig_as_u32(4)];
 memcpy(t69, t68, sizeof(zig_u64 [zig_as_u32(4)]));
 zig_u64 const t70 = t69[zig_as_u32(3)];
 zig_u64 const t71 = math_rotl__anon_1445(t70);
 (*t67) = t71;
 /* file:15:5 */
 /* file:15:5 */
 return t11;
}

static zig_void debug_assert(zig_bool const a0) {
 /* file:2:9 */
 {
  zig_bool const t0 = !a0;
  if (t0) {
   /* file:2:14 */
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&debug_assert__anon_1446), zig_as_u32(24)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  } else {
   goto zig_block_0;
  }
 }
 zig_block_0:;
 return;
}

static zig_void rand_Random_init__anon_747_gen_fill(zig_void * const a0, zig_L_u8 const a1) {
 /* file:2:17 */
 /* file:3:17 */
 zig_usize const t0 = (zig_usize )a0;
 zig_usize const t1 = t0 & zig_as_u32(7);
 zig_bool const t2 = t1 == zig_as_u32(0);
 {
  if (t2) {
   goto zig_block_0;
  } else {
   builtin_default_panic((zig_L_u8 ){(zig_u8 const * )((zig_u8 const * )&rand_Random_init__anon_747_gen_fill__anon_1447), zig_as_u32(19)}, ((zig_S_builtin_StackTrace__277 * )NULL), (zig_Q_usize ){ .payload = zig_as_u32(0xaaaaaaaa), .is_null = zig_true });
  }
 }
 zig_block_0:;
 zig_void * const t3 = (zig_void * )a0;
 zig_S_rand_Xoshiro256__255 * const t4 = (zig_S_rand_Xoshiro256__255 * )t3;
 /* var:self */
 /* file:4:17 */
 /* file:4:23 */
 rand_Xoshiro256_fill(t4, a1);
 return;
}

static zig_u32 mem_readIntNative__anon_1433(zig_A_u8_4 const * const a0) {
 /* file:2:5 */
 zig_u32 const * const t0 = (zig_u32 const * )a0;
 zig_u32 const t1 = (*t0);
 /* file:2:5 */
 return t1;
}

static zig_u64 mem_readIntSliceNative__anon_1434(zig_L_u8 const a0) {
 /* file:2:5 */
 /* file:3:5 */
 /* file:3:11 */
 zig_usize const t0 = a0.len;
 zig_u32 t1;
 memcpy(&t1, &t0, sizeof(zig_u32 ));
 t1 = zig_wrap_u32(t1, zig_as_u8(32));
 zig_bool const t2 = t1 >= zig_as_u32(8);
 debug_assert(t2);
 /* file:4:5 */
 zig_u64 t3;
 /* file:4:25 */
 zig_L_u8 t4;
 t4 = a0;
 zig_L_u8 const * const t5 = (zig_L_u8 const * )&t4;
 zig_L_u8 const t6 = (*t5);
 zig_u8 const * const t7 = t6.ptr;
 zig_u8 const * const t8 = (zig_u8 const * )(((uintptr_t)t7) + (zig_as_u32(0)*sizeof(zig_u8 )));
 zig_A_u8_8 const * const t9 = (zig_A_u8_8 const * )t8;
 zig_usize const t10 = t6.len;
 zig_bool const t11 = zig_as_u32(8) <= t10;
 {
  if (t11) {
   goto zig_block_0;
  } else {
   zig_breakpoint();
   zig_unreachable();
  }
 }
 zig_block_0:;
 zig_u64 const t12 = mem_readIntNative__anon_1448(t9);
 t3 = t12;
 /* file:4:5 */
 return t3;
}

static zig_u8 mem_readIntNative__anon_1435(zig_A_u8_1 const * const a0) {
 /* file:2:5 */
 zig_u8 const * const t0 = (zig_u8 const * )a0;
 zig_u8 const t1 = (*t0);
 /* file:2:5 */
 return t1;
}

static zig_u64 math_rotl__anon_1444(zig_u64 const a0) {
 /* file:2:9 */
 /* file:11:16 */
 /* file:14:13 */
 /* file:16:13 */
 /* file:16:25 */
 zig_bool const t0 = math_isPowerOfTwo__anon_1449();
 if (t0) {
  /* file:17:13 */
  /* file:17:40 */
  /* var:ar */
  /* file:18:13 */
  zig_u64 const t1 = zig_shlw_u64(a0, zig_as_u8(23), zig_as_u8(64));
  zig_u64 const t2 = zig_shr_u64(a0, zig_as_u8(41));
  zig_u64 const t3 = t1 | t2;
  /* file:18:13 */
  return t3;
 } else {
  /* file:20:13 */
  /* file:21:13 */
  /* file:21:23 */
  zig_u64 const t4 = math_shl__anon_1453(a0);
  /* file:21:39 */
  zig_u64 const t5 = math_shr__anon_1454(a0);
  zig_u64 const t6 = t4 | t5;
  /* file:21:13 */
  return t6;
 }
}

static zig_u64 math_rotl__anon_1445(zig_u64 const a0) {
 /* file:2:9 */
 /* file:11:16 */
 /* file:14:13 */
 /* file:16:13 */
 /* file:16:25 */
 zig_bool const t0 = math_isPowerOfTwo__anon_1455();
 if (t0) {
  /* file:17:13 */
  /* file:17:40 */
  /* var:ar */
  /* file:18:13 */
  zig_u64 const t1 = zig_shlw_u64(a0, zig_as_u8(45), zig_as_u8(64));
  zig_u64 const t2 = zig_shr_u64(a0, zig_as_u8(19));
  zig_u64 const t3 = t1 | t2;
  /* file:18:13 */
  return t3;
 } else {
  /* file:20:13 */
  /* file:21:13 */
  /* file:21:23 */
  zig_u64 const t4 = math_shl__anon_1456(a0);
  /* file:21:39 */
  zig_u64 const t5 = math_shr__anon_1457(a0);
  zig_u64 const t6 = t4 | t5;
  /* file:21:13 */
  return t6;
 }
}

static zig_u64 mem_readIntNative__anon_1448(zig_A_u8_8 const * const a0) {
 /* file:2:5 */
 zig_u64 const * const t0 = (zig_u64 const * )a0;
 zig_u64 const t1 = (*t0);
 /* file:2:5 */
 return t1;
}

static zig_bool math_isPowerOfTwo__anon_1449(zig_void) {
 /* file:2:5 */
 /* file:2:11 */
 debug_assert(zig_true);
 /* file:3:5 */
 /* file:3:5 */
 return zig_true;
}

static zig_u64 math_shl__anon_1453(zig_u64 const a0) {
 /* file:2:5 */
 /* file:2:34 */
 /* file:4:5 */
 /* file:5:13 */
 /* file:11:17 */
 /* file:12:13 */
 /* file:12:40 */
 /* var:casted_shift_amt */
 /* file:16:9 */
 /* file:17:13 */
 /* file:22:5 */
 zig_u64 const t0 = zig_shlw_u64(a0, zig_as_u8(23), zig_as_u8(64));
 /* file:22:5 */
 return t0;
}

static zig_u64 math_shr__anon_1454(zig_u64 const a0) {
 /* file:2:5 */
 /* file:2:34 */
 /* file:4:5 */
 /* file:5:13 */
 /* file:11:17 */
 /* file:12:13 */
 /* file:12:40 */
 /* var:casted_shift_amt */
 /* file:16:9 */
 /* file:17:13 */
 /* file:22:5 */
 zig_u64 const t0 = zig_shr_u64(a0, zig_as_u8(41));
 /* file:22:5 */
 return t0;
}

static zig_bool math_isPowerOfTwo__anon_1455(zig_void) {
 /* file:2:5 */
 /* file:2:11 */
 debug_assert(zig_true);
 /* file:3:5 */
 /* file:3:5 */
 return zig_true;
}

static zig_u64 math_shl__anon_1456(zig_u64 const a0) {
 /* file:2:5 */
 /* file:2:34 */
 /* file:4:5 */
 /* file:5:13 */
 /* file:11:17 */
 /* file:12:13 */
 /* file:12:40 */
 /* var:casted_shift_amt */
 /* file:16:9 */
 /* file:17:13 */
 /* file:22:5 */
 zig_u64 const t0 = zig_shlw_u64(a0, zig_as_u8(45), zig_as_u8(64));
 /* file:22:5 */
 return t0;
}

static zig_u64 math_shr__anon_1457(zig_u64 const a0) {
 /* file:2:5 */
 /* file:2:34 */
 /* file:4:5 */
 /* file:5:13 */
 /* file:11:17 */
 /* file:12:13 */
 /* file:12:40 */
 /* var:casted_shift_amt */
 /* file:16:9 */
 /* file:17:13 */
 /* file:22:5 */
 zig_u64 const t0 = zig_shr_u64(a0, zig_as_u8(19));
 /* file:22:5 */
 return t0;
}
static zig_u8 generator_generate_heightmap__anon_276[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_generate_heightmap__anon_281[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_generate_heightmap__anon_282[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_generate_heightmap__anon_283[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_generate_heightmap__anon_284[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_generate_heightmap__anon_285[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_generate_heightmap__anon_286[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_287[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_288[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_289[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_290[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_291[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_292[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_smooth_heightmap__anon_293[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_294[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_295[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_smooth_heightmap__anon_296[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_297[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_298[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_299[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_300[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_strata__anon_301[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_302[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_303[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_strata__anon_304[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_make_caves__anon_305[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_make_ores__anon_306[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_make_ores__anon_307[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_make_ores__anon_308[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_water__anon_309[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_water__anon_310[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_water__anon_311[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_fill_water__anon_312[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_water__anon_313[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_water__anon_314[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_lava__anon_315[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_lava__anon_316[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fill_lava__anon_317[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_318[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_319[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_320[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_321[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_322[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_323[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_surface__anon_324[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_surface__anon_325[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_surface__anon_326[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_plants__anon_327[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_plants__anon_328[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_plants__anon_329[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_noise1__anon_333[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_noise1__anon_334[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_noise2__anon_335[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_noise2__anon_336[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 perlin_onoise__anon_337[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_getIdx__anon_338[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_getIdx__anon_339[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_getIdx__anon_340[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_getIdx__anon_341[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_getIdx__anon_342[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_cave__anon_696[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_cave__anon_698[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_cave__anon_699[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_cave__anon_700[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_cave__anon_701[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_cave__anon_702[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_cave__anon_703[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_cave__anon_704[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_vein__anon_705[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_vein__anon_706[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_vein__anon_707[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_vein__anon_708[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_create_vein__anon_709[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_711[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_713[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_714[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_715[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_716[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_717[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_718[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_719[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_720[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_flowers__anon_721[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_flowers__anon_722[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_723[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_flowers__anon_724[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_flowers__anon_725[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_726[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_727[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_728[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_729[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_730[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_731[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_732[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_733[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_734[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_mushrooms__anon_735[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_736[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_737[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_738[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_739[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_740[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_741[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_742[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_743[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_744[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_create_tree__anon_745[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_create_tree__anon_746[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 target_mips_cpu_mips32__anon_1172[zig_as_u32(7)] = {zig_as_u8(109),zig_as_u8(105),zig_as_u8(112),zig_as_u8(115),zig_as_u8(51),zig_as_u8(50),zig_as_u8(0)};
static zig_u8 rand_Random_float__anon_695__anon_1202[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 rand_Random_float__anon_695__anon_1203[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 rand_Random_float__anon_695__anon_1204[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1205[zig_as_u32(50)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(112),zig_as_u8(97),zig_as_u8(114),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(110),zig_as_u8(103),zig_as_u8(32),zig_as_u8(112),zig_as_u8(111),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(111),zig_as_u8(117),zig_as_u8(116),zig_as_u8(32),zig_as_u8(111),zig_as_u8(102),zig_as_u8(32),zig_as_u8(98),zig_as_u8(111),zig_as_u8(117),zig_as_u8(110),zig_as_u8(100),zig_as_u8(115)};
static zig_u8 generator_fillOblateSpheroid__anon_1206[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1207[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1208[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1209[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1210[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1211[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1212[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1213[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1214[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1215[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1216[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1217[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1218[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1219[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1220[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1221[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1222[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_fillOblateSpheroid__anon_1223[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_fillOblateSpheroid__anon_1224[zig_as_u32(50)] = {zig_as_u8(97),zig_as_u8(116),zig_as_u8(116),zig_as_u8(101),zig_as_u8(109),zig_as_u8(112),zig_as_u8(116),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(99),zig_as_u8(97),zig_as_u8(115),zig_as_u8(116),zig_as_u8(32),zig_as_u8(110),zig_as_u8(101),zig_as_u8(103),zig_as_u8(97),zig_as_u8(116),zig_as_u8(105),zig_as_u8(118),zig_as_u8(101),zig_as_u8(32),zig_as_u8(118),zig_as_u8(97),zig_as_u8(108),zig_as_u8(117),zig_as_u8(101),zig_as_u8(32),zig_as_u8(116),zig_as_u8(111),zig_as_u8(32),zig_as_u8(117),zig_as_u8(110),zig_as_u8(115),zig_as_u8(105),zig_as_u8(103),zig_as_u8(110),zig_as_u8(101),zig_as_u8(100),zig_as_u8(32),zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114)};
static zig_u8 generator_fillOblateSpheroid__anon_1225[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1226[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_fillOblateSpheroid__anon_1227[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1229[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1230[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1231[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1232[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1233[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1234[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1235[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1236[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1237[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1238[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1239[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1240[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1241[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1242[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1243[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1244[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1245[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1246[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1247[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1248[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1249[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1250[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1251[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1252[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1253[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1254[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1255[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1256[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1257[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1258[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1259[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1260[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1261[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1262[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1263[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1264[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1265[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1266[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1267[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1268[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1269[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1270[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1271[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1272[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1273[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1274[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1275[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1276[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1277[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1278[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1279[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1280[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1281[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1282[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1283[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};
static zig_u8 generator_growTree__anon_1284[zig_as_u32(16)] = {zig_as_u8(105),zig_as_u8(110),zig_as_u8(116),zig_as_u8(101),zig_as_u8(103),zig_as_u8(101),zig_as_u8(114),zig_as_u8(32),zig_as_u8(111),zig_as_u8(118),zig_as_u8(101),zig_as_u8(114),zig_as_u8(102),zig_as_u8(108),zig_as_u8(111),zig_as_u8(119)};