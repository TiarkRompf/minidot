Require Import dot_storeless_tidy.

Definition dnone := dty TTop. (* TODO it would cleaner to add a dnone to DOT's Inductive dm *)
Definition TAlias(l: lb)(T: ty) := TMem l T T.

Fixpoint one_step(t: tm): option tm := match t with
(* ST_AppAbs *)
| (tapp (tvar (VObj f)) l (tvar (VObj x))) => match (index l (dms_to_list (subst_dms f f))) with
  | Some (dfun T1 T2 t12) => Some (subst_tm x t12)
  | _ => None
  end
(* ST_App2 *)
| (tapp (tvar (VObj f)) l t2) => match (one_step t2) with
  | Some t2' => Some (tapp (tvar (VObj f)) l t2')
  | None => None
  end
(* ST_App1 *)
| (tapp t1 l t2) => match (one_step t1) with
  | Some t1' => Some (tapp t1' l t2)
  | None => None
  end
(* default: stuck *)
| _ => None
end.

(* returns how many steps were done & what term was reached after that many steps *)
Fixpoint n_steps(n: nat)(t: tm): (nat * tm) := match n with
| S m => match (one_step t) with
  | Some t' => let (m', t'') := n_steps m t' in (S m', t'')
  | None => (0, t)
  end
| 0 => (0, t)
end.

Definition mutrecEx: tm := (tapp (tvar (VObj (*_unusedSelf =>*)
  (dcons (dfun (*call*) (*Unit*) (TBind (*_self =>*)
    (TAnd (TAlias 1 (*C*) (TBind 
      TTop
    ))
    (TFun 2 (*new*) (*_dummy*) TTop (TSel (VarB 1 (*_self*)) 1 (*C*))))
  ) TTop (tapp (tvar (VObj (*_unusedSelf =>*)
    (dcons (dfun (*call*) (*unit*) (TSel (VarB 1 (*Unit*)) 1 (*C*)) TTop (tapp (tvar (VObj (*_unusedSelf =>*)
      (dcons (dfun (*call*) (*Lib1*) (TBind (*_self =>*)
        (TAnd (TAlias 1 (*C*) (TBind (*lib1 =>*)
          (TAnd (TAlias 3 (*C_Author*) (TBind 
            (TAnd (TFun 4 (*book*) (*u*) (TSel (VarB 6 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 5 (*C_Book*)))
            (TAnd TTop
            TTop))
          ))
          (TAnd (TFun 6 (*new_Author*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 3 (*C_Author*)))
          (TAnd (TAlias 5 (*C_Book*) (TBind 
            (TAnd (TFun 7 (*author*) (*u*) (TSel (VarB 6 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 3 (*C_Author*)))
            (TAnd TTop
            TTop))
          ))
          (TAnd (TFun 8 (*new_Book*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)))
          (TAnd (TFun 9 (*run*) (*u*) (TSel (VarB 5 (*Unit*)) 1 (*C*)) (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)))
          (TAnd TTop
          TTop))))))
        ))
        (TFun 2 (*new*) (*_dummy*) TTop (TSel (VarB 1 (*_self*)) 1 (*C*))))
      ) TTop (tapp (tvar (VObj (*_unusedSelf =>*)
        (dcons (dfun (*call*) (*lib1*) (TSel (VarB 1 (*Lib1*)) 1 (*C*)) TTop (tapp (tvar (VarB 0 (*lib1*))) 9 (*run*) (tvar (VarB 4 (*unit*)))))
        dnil)
      )) 0 (*call*) (tapp (tvar (VarB 0 (*Lib1*))) 2 (*new*) (tvar (VObj dnil)))))
      dnil)
    )) 0 (*call*) (tvar (VObj (*_self =>*)
      (dcons (dfun (*new*) (*_dummy*) TTop (TSel (VarB 1 (*_self*)) 1 (*C*)) (tvar (VObj (*lib1 =>*)
        (dcons (dfun (*run*) (*u*) (TSel (VarB 5 (*Unit*)) 1 (*C*)) (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)) (tapp (tvar (VObj (*_unusedSelf =>*)
          (dcons (dfun (*call*) (*a*) (TSel (VarB 2 (*lib1*)) 3 (*C_Author*)) (TSel (VarB 3 (*lib1*)) 5 (*C_Book*)) (tapp (tvar (VarB 0 (*a*))) 4 (*book*) (tvar (VarB 6 (*unit*)))))
          dnil)
        )) 0 (*call*) (tapp (tapp (tvar (VarB 1 (*lib1*))) 8 (*new_Book*) (tvar (VObj dnil))) 7 (*author*) (tvar (VarB 4 (*unit*))))))
        (dcons (dfun (*new_Book*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)) (tvar (VObj 
          (dcons (dfun (*author*) (*u*) (TSel (VarB 7 (*Unit*)) 1 (*C*)) (TSel (VarB 3 (*lib1*)) 3 (*C_Author*)) (tapp (tvar (VarB 3 (*lib1*))) 6 (*new_Author*) (tvar (VObj dnil))))
          (dcons dnone
          (dcons dnone
          (dcons dnone
          (dcons dnone
          (dcons dnone
          (dcons dnone
          (dcons dnone
          dnil))))))))
        )))
        (dcons dnone
        (dcons (dfun (*new_Author*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 3 (*C_Author*)) (tvar (VObj 
          (dcons (dfun (*book*) (*u*) (TSel (VarB 7 (*Unit*)) 1 (*C*)) (TSel (VarB 3 (*lib1*)) 5 (*C_Book*)) (tapp (tvar (VarB 3 (*lib1*))) 8 (*new_Book*) (tvar (VObj dnil))))
          (dcons dnone
          (dcons dnone
          (dcons dnone
          (dcons dnone
          dnil)))))
        )))
        (dcons (dty (*C_Book*) (TBind 
          (TAnd (TFun 7 (*author*) (*u*) (TSel (VarB 6 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 3 (*C_Author*)))
          (TAnd TTop
          TTop))
        ))
        (dcons dnone
        (dcons (dty (*C_Author*) (TBind 
          (TAnd (TFun 4 (*book*) (*u*) (TSel (VarB 6 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 5 (*C_Book*)))
          (TAnd TTop
          TTop))
        ))
        (dcons dnone
        (dcons dnone
        (dcons dnone
        dnil))))))))))
      )))
      (dcons (dty (*C*) (TBind (*lib1 =>*)
        (TAnd (TAlias 3 (*C_Author*) (TBind 
          (TAnd (TFun 4 (*book*) (*u*) (TSel (VarB 5 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 5 (*C_Book*)))
          (TAnd TTop
          TTop))
        ))
        (TAnd (TFun 6 (*new_Author*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 3 (*C_Author*)))
        (TAnd (TAlias 5 (*C_Book*) (TBind 
          (TAnd (TFun 7 (*author*) (*u*) (TSel (VarB 5 (*Unit*)) 1 (*C*)) (TSel (VarB 2 (*lib1*)) 3 (*C_Author*)))
          (TAnd TTop
          TTop))
        ))
        (TAnd (TFun 8 (*new_Book*) (*_dummy*) TTop (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)))
        (TAnd (TFun 9 (*run*) (*u*) (TSel (VarB 4 (*Unit*)) 1 (*C*)) (TSel (VarB 1 (*lib1*)) 5 (*C_Book*)))
        (TAnd TTop
        TTop))))))
      ))
      (dcons dnone
      dnil)))
    ))))
    dnil)
  )) 0 (*call*) (tapp (tvar (VarB 0 (*Unit*))) 2 (*new*) (tvar (VObj dnil)))))
  dnil)
)) 0 (*call*) (tvar (VObj (*_self =>*)
  (dcons (dfun (*new*) (*_dummy*) TTop (TSel (VarB 1 (*_self*)) 1 (*C*)) (tvar (VObj dnil)))
  (dcons (dty (*C*) (TBind 
    TTop
  ))
  (dcons dnone
  dnil)))
))).

Eval cbv in (n_steps 100 mutrecEx).




