theories/lang/subst_map.vo theories/lang/subst_map.glob theories/lang/subst_map.v.beautified theories/lang/subst_map.required_vo: theories/lang/subst_map.v 
theories/lang/subst_map.vio: theories/lang/subst_map.v 
theories/lang/subst_map.vos theories/lang/subst_map.vok theories/lang/subst_map.required_vos: theories/lang/subst_map.v 
theories/lang/hazel.vo theories/lang/hazel.glob theories/lang/hazel.v.beautified theories/lang/hazel.required_vo: theories/lang/hazel.v theories/lang/subst_map.vo
theories/lang/hazel.vio: theories/lang/hazel.v theories/lang/subst_map.vio
theories/lang/hazel.vos theories/lang/hazel.vok theories/lang/hazel.required_vos: theories/lang/hazel.v theories/lang/subst_map.vos
theories/logic/iEff.vo theories/logic/iEff.glob theories/logic/iEff.v.beautified theories/logic/iEff.required_vo: theories/logic/iEff.v theories/lang/hazel.vo
theories/logic/iEff.vio: theories/logic/iEff.v theories/lang/hazel.vio
theories/logic/iEff.vos theories/logic/iEff.vok theories/logic/iEff.required_vos: theories/logic/iEff.v theories/lang/hazel.vos
theories/logic/sem_types.vo theories/logic/sem_types.glob theories/logic/sem_types.v.beautified theories/logic/sem_types.required_vo: theories/logic/sem_types.v theories/lang/hazel.vo theories/logic/iEff.vo
theories/logic/sem_types.vio: theories/logic/sem_types.v theories/lang/hazel.vio theories/logic/iEff.vio
theories/logic/sem_types.vos theories/logic/sem_types.vok theories/logic/sem_types.required_vos: theories/logic/sem_types.v theories/lang/hazel.vos theories/logic/iEff.vos
theories/logic/sem_typed.vo theories/logic/sem_typed.glob theories/logic/sem_typed.v.beautified theories/logic/sem_typed.required_vo: theories/logic/sem_typed.v theories/lang/hazel.vo theories/logic/iEff.vo theories/logic/sem_types.vo
theories/logic/sem_typed.vio: theories/logic/sem_typed.v theories/lang/hazel.vio theories/logic/iEff.vio theories/logic/sem_types.vio
theories/logic/sem_typed.vos theories/logic/sem_typed.vok theories/logic/sem_typed.required_vos: theories/logic/sem_typed.v theories/lang/hazel.vos theories/logic/iEff.vos theories/logic/sem_types.vos
theories/logic/sem_sub_typing.vo theories/logic/sem_sub_typing.glob theories/logic/sem_sub_typing.v.beautified theories/logic/sem_sub_typing.required_vo: theories/logic/sem_sub_typing.v theories/logic/sem_types.vo theories/logic/sem_typed.vo
theories/logic/sem_sub_typing.vio: theories/logic/sem_sub_typing.v theories/logic/sem_types.vio theories/logic/sem_typed.vio
theories/logic/sem_sub_typing.vos theories/logic/sem_sub_typing.vok theories/logic/sem_sub_typing.required_vos: theories/logic/sem_sub_typing.v theories/logic/sem_types.vos theories/logic/sem_typed.vos
theories/logic/sem_operators.vo theories/logic/sem_operators.glob theories/logic/sem_operators.v.beautified theories/logic/sem_operators.required_vo: theories/logic/sem_operators.v theories/lang/hazel.vo theories/logic/sem_types.vo
theories/logic/sem_operators.vio: theories/logic/sem_operators.v theories/lang/hazel.vio theories/logic/sem_types.vio
theories/logic/sem_operators.vos theories/logic/sem_operators.vok theories/logic/sem_operators.required_vos: theories/logic/sem_operators.v theories/lang/hazel.vos theories/logic/sem_types.vos
theories/logic/compatibility.vo theories/logic/compatibility.glob theories/logic/compatibility.v.beautified theories/logic/compatibility.required_vo: theories/logic/compatibility.v theories/lang/hazel.vo theories/logic/iEff.vo theories/logic/sem_types.vo theories/logic/sem_typed.vo theories/logic/sem_sub_typing.vo theories/logic/sem_operators.vo
theories/logic/compatibility.vio: theories/logic/compatibility.v theories/lang/hazel.vio theories/logic/iEff.vio theories/logic/sem_types.vio theories/logic/sem_typed.vio theories/logic/sem_sub_typing.vio theories/logic/sem_operators.vio
theories/logic/compatibility.vos theories/logic/compatibility.vok theories/logic/compatibility.required_vos: theories/logic/compatibility.v theories/lang/hazel.vos theories/logic/iEff.vos theories/logic/sem_types.vos theories/logic/sem_typed.vos theories/logic/sem_sub_typing.vos theories/logic/sem_operators.vos
