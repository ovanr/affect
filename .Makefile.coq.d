src/lang/subst_map.vo src/lang/subst_map.glob src/lang/subst_map.v.beautified src/lang/subst_map.required_vo: src/lang/subst_map.v 
src/lang/subst_map.vio: src/lang/subst_map.v 
src/lang/subst_map.vos src/lang/subst_map.vok src/lang/subst_map.required_vos: src/lang/subst_map.v 
src/lang/hazel.vo src/lang/hazel.glob src/lang/hazel.v.beautified src/lang/hazel.required_vo: src/lang/hazel.v src/lang/subst_map.vo
src/lang/hazel.vio: src/lang/hazel.v src/lang/subst_map.vio
src/lang/hazel.vos src/lang/hazel.vok src/lang/hazel.required_vos: src/lang/hazel.v src/lang/subst_map.vos
src/logic/interp.vo src/logic/interp.glob src/logic/interp.v.beautified src/logic/interp.required_vo: src/logic/interp.v src/lang/hazel.vo src/lang/subst_map.vo
src/logic/interp.vio: src/logic/interp.v src/lang/hazel.vio src/lang/subst_map.vio
src/logic/interp.vos src/logic/interp.vok src/logic/interp.required_vos: src/logic/interp.v src/lang/hazel.vos src/lang/subst_map.vos
