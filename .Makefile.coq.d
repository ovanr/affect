src/logic/subst_map.vo src/logic/subst_map.glob src/logic/subst_map.v.beautified src/logic/subst_map.required_vo: src/logic/subst_map.v 
src/logic/subst_map.vio: src/logic/subst_map.v 
src/logic/subst_map.vos src/logic/subst_map.vok src/logic/subst_map.required_vos: src/logic/subst_map.v 
src/logic/interp.vo src/logic/interp.glob src/logic/interp.v.beautified src/logic/interp.required_vo: src/logic/interp.v src/logic/subst_map.vo
src/logic/interp.vio: src/logic/interp.v src/logic/subst_map.vio
src/logic/interp.vos src/logic/interp.vok src/logic/interp.required_vos: src/logic/interp.v src/logic/subst_map.vos
