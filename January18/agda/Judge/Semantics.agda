module Judge.Semantics where

open import Datoid
open import OPE hiding (dealLeft; dealRight)
open import Syntax
open import Judge
open import Sum
import Syntax.DBSubst as DBS
open _^^_


record Var {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(k : Kind I)(iz : Cx I) : Set where
  constructor cnt
  field
    varJ : J
  open JForm (JF varJ)
  field
    varIp : Rele (TmK F pat) (spD inputs) ^^ []
    varSb : ([] -, k) == subjects
    varOp : Rele (TmK F exp) (spD outputs) ^^ (iz ++ patsD (spD inputs) (varIp .thing))

open CEnt
open Var

substVar : ∀ {I J} {F : I → Desc I} {JF : J → JForm I}
             {k : Kind I} {iz oz : Cx I} → Morph F iz oz → Var F JF k iz -> Var F JF k oz
varJ (substVar σ x) = x .varJ
varIp (substVar σ x) = (x .varIp)
varSb (substVar σ x) = x .varSb
varOp (substVar {JF = JF} σ x) = subD (wmor σ _) (spD (JF (x .varJ) .JForm.outputs)) (x .varOp)

data Cxt {I J : Set}(F : I -> Desc I)(JF : J -> JForm I) : (iz : Cx I) -> Set where
  [] : Cxt F JF []
  _-,_ : {iz : Cx I}{k : Kind I} -> Cxt F JF iz -> Var F JF k iz -> Cxt F JF (iz -, k)

thm : ∀ {I} {F : I → Desc I} {i}{iz} (patz : DB F pat i iz) → patsDB patz == pats (translate patz .thing)
thmD : ∀ {I} {F : I → Desc I} D {iz} (pats : DeBr (DBK F pat) D iz) → patsDBD D pats == patsD D (translateD D pats .thing)
thmD (rec' (jz => j)) patz rewrite thm patz with (translate patz) | thinSplit _ jz (thinning (translate patz))
thmD (rec' (jz => j)) patz | thing ^ .(th <++= ph) | mkThinSplit th ph = refl
thmD (C %' D) (c / pats) = thmD (D c) pats
thmD (D *' E) (patsl , patsr) rewrite thmD D patsl | thmD E patsr with (translateD D patsl)
                              | (translateD E patsr) | union (thinning (translateD D patsl)) (thinning (translateD E patsr))
... | thing ^ .(lope c <&= th) | thing₁ ^ .(rope c <&= th) | mkUnion c th = refl
thmD One' pats = refl
thm {F = F} {i = i} [ x ] = thmD (F i) x
thm (var {jz = jz} x x₁) rewrite thmD (spD jz) x₁ with (translateD (spD jz) x₁) | union x (thinning (translateD (spD jz) x₁))
... | thing ^ .(rope c <&= th) | mkUnion c th = refl
thm (pat x x₁) = refl

toVar : ∀ {I J} {F : I → Desc I} {JF : J → JForm I}
             {k : Kind I} {iz : Cx I} → CEnt F JF k iz -> Var F JF k iz
toVar {F = F} {JF = JF} {k} {iz} x = cnt (x .varJ) (translateD (spD inputs) (x .varIp)) (x .varSb)
                (replace (\ jz → Rele (TmK F exp) (spD outputs) ^^ (iz ++ jz)) (thmD (spD inputs) (varIp x)) (translateD (spD outputs) (x .varOp)))
 where
      open JForm (JF (x .varJ))

appendCE' : ∀ {I J} {F : I → Desc I} {JF : J → JForm I}
             {vz : Bwd (Kind I)} {iz : Cx I} →
           Cxt F JF vz →
           CExt F JF vz iz → Cxt F JF (vz ++ iz)
appendCE' le [] = le
appendCE' {JF = JF} {vz} {iz} le (re -, x) = appendCE' le re -, toVar x
  where
      open JForm (JF (x .varJ))

appendCE : ∀ {I J} {F : I → Desc I} {JF : J → JForm I}
             {vz invz : Bwd (Kind I)} {iz : Cx I} →
           Cxt F JF vz →
           Morph F invz vz →
           CExt F JF invz iz → Cxt F JF (vz ++ iz)
appendCE le intz [] = le
appendCE le intz (x -, v) = appendCE le intz x -, substVar (wmor intz _) (toVar v)


dealLR' : {I : Set}(jz : Bwd I) -> Deal [] jz jz
dealLR' [] = dzz
dealLR' (jz -, j) = d's (dealLR' jz)



module Semantics {I : Set}(F : I -> Desc I) where
  Tms : Cx I → Cx I → Set
  Tms vz kz = Rele (TmK F exp) (spD kz) ^^ vz

  toSub : ∀ {iz} {oz} → Tms iz oz → Morph F oz iz
  toSub {_} {invz} intz = mkMorph oe (dealLR' invz) (enips {jz = invz} intz)

  -- Andrea: extending with iz on the right makes the recursion go
  -- though the rec case.
  -- However I'm not sure if "patsDB ps ++ iz" makes sense as a typed
  -- context in general: could the types of "patsDB ps" mention the
  -- variables "iz" in principle?
  patsIntoExpr : ∀ {iz i} (ps : DB F pat i iz) -> Tm F exp i ^^ (patsDB ps ++ iz)
  patsIntoExprD : ∀ {iz} D → (ps : DeBr (DBK F pat) D iz) → Rele (TmK F exp) D ^^ (patsDBD D ps ++ iz)
  patsIntoExpr {iz} {i} [ x ] = [ patsIntoExprD (F i) x  ]^
  patsIntoExpr (var {jz} x tz) = var^ (x <&= oinr) (patsIntoExprD (spD jz) tz)
  patsIntoExpr (pat {jz} x th) = var^ oinl (subD (cmor (omor F th) (omor F (oinr))) (spD jz) (idSpine F {jz} ^ oi))
  patsIntoExprD {iz} (rec' (kz => k)) ps = _ !-^ replace (\ iz -> Tm F exp k ^^ iz) (sym (assoc++ (patsDB ps) iz kz)) (patsIntoExpr ps)
  patsIntoExprD (C %' D) (c / ps) = c /^ patsIntoExprD (D c) ps
  patsIntoExprD {iz} (D *' E) (psl , psr) = subD (wmor (omor F oinl) iz) D (patsIntoExprD D psl)
                                         ,^ subD (wmor (omor F oinr) iz) E (patsIntoExprD E psr)
  patsIntoExprD One' ps = done^

  fillIn : ∀ (iz : Cx I) {vz : Cx I} →
             (patz : DeBr (DBK F pat) (spD iz) []) →
             Tms vz (patsDBD (spD iz) patz) → Tms vz iz
  fillIn ins patz es = let r = (patsIntoExprD (spD ins) patz) in
                       subD (toSub es) (spD ins) r

  dealLeft : {vz iz jz kz : Cx I} → Deal iz jz kz → Tms vz kz → Tms vz iz
  dealLeft dzz     tz0 = tz0
  dealLeft (ds' d) tz0 = let tz , t = proj^ tz0 in (dealLeft d tz) ,^ t
  dealLeft (d's d) tz0 = let tz , t = proj^ tz0 in dealLeft d tz

  dealRight : {vz iz jz kz : Cx I} → Deal iz jz kz → Tms vz kz → Tms vz jz
  dealRight dzz     tz0 = done^
  dealRight (ds' d) tz0 = let tz , t = proj^ tz0 in (dealRight d tz)
  dealRight (d's d) tz0 = let tz , t = proj^ tz0 in (dealRight d tz) ,^ t

  dealVar : ∀ {k}{sz1 : Bwd (Kind I)}
         {sz' : Bwd (Kind I)} →
         Deal sz' ([] -, k) sz1 → The k sz1
  dealVar (ds' d) = o' (dealVar d)
  dealVar (d's d) = os oe

  module _ {J : Set}(JF : J -> JForm I) where

    splitSubjects : {vz iz sbvz kz mz' sz' : Cx I}
                  → Tms vz sbvz → Subjects F JF iz sbvz mz' sz' kz
                  → Tms vz mz' * Tms vz sz' * Tms (vz ++ iz) kz
    splitSubjects tz [] = done^ , tz , done^
    splitSubjects {vz} {iz} tz (pick {jz' = jz'}{jz = jz} sbz sb args) with splitSubjects tz sbz
    ... | tmz , tsz' , tkz = (tmz ,^ s) , dealLeft sb tsz' , (tkz ,^ (_ !-^ u))
     where
       s = proj^ (dealRight sb tsz') .snd
       r = translateD (spD jz') (DBS.idSpine args)
       u = sub (replace (Morph F _) (sym (assoc++ vz iz jz)) (wmor (toSub tsz') (iz ++ jz)))
                                         (var^ (dealVar sb <&= oinl) (r .thing ^ (r .thinning <&= oinr)))

    record JudgmentArity (j : J) : Set where
      constructor con
      open JForm (JF j)
      field
        {vz} : Cx I
        cxt : Cxt F JF vz
      field
        ipTms : Tms vz inputs
        sbTms : Tms vz subjects
        opTms : Tms vz outputs

    module _ (RelF : (j : J) → JudgmentArity j → Set) where

      ruleSem : ∀ {j} → Rule F JF j → Set
      ruleSem {j} r
        = ∀ {vz} {G : Cxt F JF vz}
             (let ipvz = (patsDBD (spD inputs)  (r .inpats)))
             (let sbvz = (patsDBD (spD subjects) (r .sbpats)))
             (iptz : Tms vz (patsDBD (spD inputs)  (r .inpats)))
             (sbtz : Tms vz (patsDBD (spD subjects) (r .sbpats))) →
             (prems : premises G iptz sbtz (r .deduction)) →
             (let _ , tms , a = (projOuts {vz} {ipvz} {sbvz} G iptz sbtz {r .deduction} prems)) →
               RelF j ( (con G (fillIn inputs (r .inpats) iptz )
                             ( (fillIn subjects (r .sbpats) sbtz) )
                             (subD (toSub tms) (spD outputs) (translateD (spD outputs) a))) )
        where
          open JForm (JF j)

          premises : ∀ {vz invz sbvz A} → Cxt F JF vz → Tms vz invz -> Tms vz sbvz -> Prems F JF invz sbvz A → Set
          premises G intz sbtz      (return _ _) = One
          premises G intz sbtz      fail         = Zero
          premises {vz} {invz} {sbvz} G intz sbtz
            (prem {iz} cext j' j'intz' {mz'} {sz'} sbchooser opPatz psD)
            = Sg (Tms vz (patsDBD (spD outputs') opPatz))
              \ evarz →
                let
                  j'intz = translateD (spD (JForm.inputs (JF j'))) j'intz'
                  j'optz = patsIntoExprD (spD (JForm.outputs (JF j'))) opPatz
                  evars = toSub evarz
                  mz'tz , sz'tz , j'sbtz = splitSubjects sbtz sbchooser
                  ints = toSub intz
                  G,iz : Cxt F JF (vz ++ iz)
                  G,iz = appendCE G ints cext
                  newintz = (spine ((enips {jz = _}                              intz   +A+
                                    enips {jz = mz'}                             mz'tz) +A+
                                    enips {jz = (patsDBD (spD outputs') opPatz)} evarz))
                in
                 RelF j'
                  (con G,iz
                        (subD (wmor ints  iz) (spD (JForm.inputs   (JF j'))) j'intz)
                        (                                                    j'sbtz)
                        (subD (wmor evars iz) (spD (JForm.outputs  (JF j'))) j'optz))
                 * premises G newintz sz'tz psD
           where
             outputs' = (JF j' .JForm.outputs)

          projOuts : ∀ {vz invz sbvz A} → (G : Cxt F JF vz)
                     → (intz : Tms vz invz) (sbtz : Tms vz sbvz) {psD : Prems F JF invz sbvz A}
                     → premises G intz sbtz psD -> Sg (Cx I) \ iz → Tms vz iz * A iz
          projOuts G intz sbtz {return refl a} ps = _ , (intz , a)
          projOuts G intz sbtz {fail} ()
          projOuts G intz sbtz {prem cext j inz sbz opz psD} (evarz , call , rest)
                   = projOuts G _ _ {psD} rest
