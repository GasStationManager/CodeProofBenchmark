import Mathlib


def solveAdd (a b:Int): Int
:= b-a

theorem solveAdd_correct (a b: Int): a + (solveAdd a b) =b
:= by simp[solveAdd]

def solveAdd0(a:Int): Int
:= -a

theorem solveAdd0_correct(a: Int): a +(solveAdd0 a)=0
:= by simp[solveAdd0]

def solveSub(a b:Int): Int
:= a-b

theorem solveSub_correct(a b:Int): a - (solveSub a b)=b
:= by simp[solveSub]

def solve1x1(a b: Rat): Option Rat :=
  if a = 0 then
    if b=0 then
      some 0
    else
      none
  else
    some (b/a)

theorem solve1x1_correct(a b:Rat): (∃ x, a*x=b) -> a * (solve1x1 a b).get! =b
:= by
    intro hsol
    simp[solve1x1]
    split_ifs
    next hb=>simp[hb]
    next ha hb=> simp[ha] at hsol; rw[hsol] at hb; contradiction
    next ha=>
      simp
      simp[Rat.div_def]
      simp[Rat.mul_comm b]
      simp[← Rat.mul_assoc]
      have: a*a.inv=1 :=by{
        have hainv: a⁻¹ = a.inv :=by {
          exact rfl
        }
        rw[← hainv]
        rw[Rat.mul_inv_cancel]
        assumption
      }
      simp[this]

theorem solve1x1_none(a b:Rat): (Not (∃ x, a*x=b)) -> solve1x1 a b=none
:= by
    intro h
    simp[solve1x1]
    split_ifs
    next ha hb=> simp[ha] at h;rw[hb] at h; contradiction
    next=>rfl
    next ha=>
      contrapose! h
      use b/a
      exact mul_div_cancel₀ b ha

def solveMul(a: Rat): Rat
:= if a=0 then 0 else 1/a

theorem solveMul_correct(a:Rat): (∃ x, a*x=1)->a * (solveMul a)=1
:= by
    intro h
    simp[solveMul]
    split
    next ha=>
      simp[ha] at h
    next ha=>
      exact Rat.mul_inv_cancel a ha

theorem solveMul_nosol (a:Rat): (Not (∃ x, a*x=1)) ->solveMul a =0
:= by
    intro h
    simp[solveMul]
    contrapose! h
    use 1/a
    exact mul_one_div_cancel h

def solveDiv(a b:Rat) (ha: a≠ 0)(hb: b≠ 0): Rat
:= a/b

theorem solveDiv_correct(a b:Rat)(ha:a≠ 0)(hb: b≠ 0):
a / (solveDiv a b ha hb)= b
:= by
    simp[solveDiv]
    rw[← div_mul]
    rw[div_self (by simp[ha])]
    simp

def isPrime(a: Nat): Bool
:=
  if a<=1 then false
  else
    let rec helper (cur: Nat):Bool:=
      if cur>=a then true
      else if a%cur=0 then false
      else helper (cur+1)
      termination_by a-cur
      decreasing_by{
        simp_wf
        have hacur: a>cur:=by omega
        exact Nat.sub_succ_lt_self a cur hacur
      }
    helper 2


theorem isPrime_correct(a: Nat):
  (isPrime a) <-> Nat.Prime a := by{
    constructor
    · {
      unfold isPrime
      split
      simp
      have: ∀ cur:Nat, cur>=2->(∀x:Nat, (x>=2 ∧  x< cur)-> a%x !=0) ->isPrime.helper a cur ->a.Prime:=by {
        intro cur
        intro hcur2
        induction cur using isPrime.helper.induct
        exact a
        next ha1 c hcga =>
          have hhelp: isPrime.helper a c =true:=by {
            unfold isPrime.helper
            simp[hcga]
          }
          simp[hhelp]
          contrapose!
          intro hnp

          apply Nat.exists_dvd_of_not_prime2 at hnp
          rcases hnp with ⟨ k, hnp'⟩
          use k
          simp[hnp']
          omega
          omega


        next ha c hca hmod =>
          have hhelp: isPrime.helper a c=false:=by{
            unfold isPrime.helper
            simp[hmod,hca]
          }
          simp[hhelp]

        next ha c hca hmod ih =>
          unfold isPrime.helper
          split
          simp
          have: c>=a :=by assumption
          contradiction
          have: c+1>=2 :=by omega
          simp[ this] at ih
          simp
          intro hx
          apply ih
          intro x
          intro hx2
          intro hxlt
          cases hc1x: c-x

          have: c=x :=by {
            omega

          }
          rw[← this]
          assumption
          have: x<c :=by{
            omega
          }
          apply hx
          assumption
          assumption
        }


      apply this
      omega
      intro x
      omega

    }
    next=>
      contrapose!
      unfold isPrime
      split
      simp
      have: a<=1 :=by assumption
      have ha2: a ≠  2 :=by omega
      have ha3: a≠ 3 :=by omega
      intro hp
      have h5p: 5<=a :=by {
        exact Nat.Prime.five_le_of_ne_two_of_ne_three hp ha2 ha3 --Prime.five_le_of_ne_two_of_ne_three a hp ha2 ha3
      }
      omega
      have: ∀cur: Nat, cur>=2 ->isPrime.helper a cur ≠ true ->¬ a.Prime :=by{
        intro cur
        intro hcur2
        induction cur using isPrime.helper.induct
        exact a
        next ha1 x hxa=>
          unfold isPrime.helper
          simp[hxa]


        next ha1 x hxa hmod =>
          unfold isPrime.helper
          simp[hxa,hmod]
          have :x ∣ a :=by omega
          have hxneqa: x≠ a :=by omega
          have hxneq1: x≠ 1 :=by omega
          exact Nat.not_prime_of_dvd_of_ne this hxneq1 hxneqa

        next ha1 x hxa hmod ih=>
          unfold isPrime.helper
          simp[hxa,hmod]
          simp at ih
          apply ih
          omega

      }
      apply this
      omega

}

def modInv(a: Nat) (p:Nat)(hp:p.Prime): Option Nat
:=
  if a%p=0 then
    none
  else
    let expn:Nat := p-2
    some ( (a^expn) %p)

theorem modInv_correct(a:Nat) (p:Nat)(hp:p.Prime):
  (∃ x:Nat, (a*x)%p=1)->(a*(modInv a p hp).get!)%p=1 :=by{
    intro hexist
    have han0: a%p ≠ 0:=by{
      contrapose! hexist
      intro x
      have: (a*x)%p =(a%p *x)%p:=by{
        simp[Nat.mod_mul_mod]
        --exact Eq.symm (Nat.mod_mul_mod a x ↑p)
      }
      rw[hexist] at this
      simp[this]
    }
    unfold modInv
    simp[han0]
    --simp[Option.get!]
    have hp2:p>=2 :=by{
      exact Nat.Prime.two_le hp
    }
    have hm:a*a^(p-2)=a^(p-1) :=by{
      calc
        a*a^(p-2)= a^1 *a^(p-2):=by {simp}
        _=a^(1+(p-2)) :=by{exact Eq.symm (Nat.pow_add a 1 (p - 2))}
        _=a^(p-1) :=by{
          have: 1+(p-2)=p-1:=by omega
          exact congrArg (HPow.hPow a) this
        }
    }
    simp[hm]

      --Fermat's little theorem
      --from Mathlib.FieldTheory.Finite
    have hcop: IsCoprime (a:Int) p :=by{
        refine Nat.isCoprime_iff_coprime.mpr ?_
        have: ¬ p ∣ a :=by{omega}
        refine Nat.coprime_iff_isRelPrime.mpr ?_
        have hrp:= (Irreducible.isRelPrime_iff_not_dvd  hp).mpr  this
        exact
          IsRelPrime.symm hrp
    }
    have:= Int.ModEq.pow_card_sub_one_eq_one  hp hcop
    have pz:((a:Int)^(p-1))%(p:Int)=1%(p:Int):=by{
      exact this
    }
    --contrapose this
    --intro hzmod
    have h1mp: 1%(p:Int)=1 :=by{
      refine Int.emod_eq_of_lt ?H1 ?H2
      omega
      omega
    }
    rw[h1mp] at pz

    norm_cast at pz

}

theorem modInv_none(a:Nat) (p:Nat)(hp:p.Prime): (Not (∃ x, (a*x)%p=1))-> modInv a p hp=none
:=by
    intro h
    simp[modInv]
    contrapose! h
    refine Nat.exists_mul_emod_eq_one_of_coprime ?hkn ?hk
    refine Nat.coprime_iff_isRelPrime.mpr ?_
    have: ¬ p ∣ a :=by{omega}
    have hrp:= (Irreducible.isRelPrime_iff_not_dvd  hp).mpr this
    exact IsRelPrime.symm hrp
    exact Nat.Prime.one_lt hp

def minFacT(a:Nat) (h: a>1)
: {x:Nat//x>1∧ x ∣ a∧ Not (∃ y>1, y∣a ∧  y<x)}
:=
  let lst:= List.range (a+1)
  let res:=lst.find? (fun x=> x>1 ∧  x∣ a)
  have : res.isSome :=by{
    refine (@List.find?_isSome _ lst fun x => decide (x > 1 ∧ x ∣ a)).mpr ?_
    use a
    constructor
    exact List.self_mem_range_succ a
    simp[h]
  }
  let r:=res.get this
  ⟨r, by{
        have hf:lst.find? (fun x=> x>1 ∧  x∣ a)=some r:=by{
          exact Eq.symm (Option.some_get this)
        }
        have lem := @List.find?_range_eq_some (a+1) _ _|>.mp hf
        simp at lem
        constructor
        simp[lem.left]
        constructor
        simp[lem.left]
        have lr:=lem.right
        rcases lr with ⟨ _,lr'⟩
        intro hy
        rcases hy with ⟨ y , hy'⟩
        have:= lr' y hy'.2.2
        rcases this <;> omega
  }⟩

def minFac(a:Nat) (h: a>1):Nat
:= minFacT a h

theorem minFac_isfac(a:Nat)(h: a>1): ( (minFac a h) ∣  a) ∧  (minFac a h>1)
:=by
    simp[minFac]
    let r:=minFacT a h
    simp[r.2]

theorem minFac_ismin(a:Nat)(h:a>1): Not (∃ y>1,( y ∣ a) ∧  y<minFac a h)
:=by
    simp[minFac]
    let r:=minFacT a h
    have:=r.2.2.2
    intro x h1 hdvd
    simp at this
    have:=this x h1 hdvd
    simp[r,this]


def midPoint (x1 y1 x2 y2: Rat):Rat × Rat
:=((x1+x2)/2, (y1+y2)/2)

def distSq( x1  y1 x2 y2: Rat):Rat:=
  (x1-x2)^2 + (y1-y2)^2

theorem midPoint_correct (x1 y1 x2 y2: Rat)
: let (xmid,ymid) :=midPoint x1 y1 x2 y2
distSq xmid ymid x1 y1=distSq xmid ymid x2 y2
∧ 4*(distSq xmid ymid x1 y1)=distSq x1  y1 x2 y2
:=by
  simp[midPoint,distSq]
  constructor <;> ring_nf


def GCD (x y: Nat): Nat :=

    if y = 0 then
      x
    else
      GCD y (x % y)
    termination_by y
    decreasing_by {
      simp_wf
      apply Nat.mod_lt _
      refine Nat.zero_lt_of_ne_zero ?_
      assumption
    }

theorem gcd_is_div (x y: Nat):
  (p: x > 0)→ ((GCD x y) ∣ x) ∧ ((GCD x y) ∣ y) := match y with
  | 0 => by  {
    simp[GCD]
  }
  | Nat.succ z =>by {
    have hyp: z.succ>0 := by {
      exact Nat.zero_lt_succ z
    }
    have ih := gcd_is_div z.succ (x % z.succ)
    have ihh := ih hyp
    have heq: GCD x z.succ = GCD z.succ (x%z.succ) :=by{
      rw[GCD.eq_def]
      tauto
    }
    intro hx
    simp[heq, ihh]
    rcases ihh.right with ⟨k, ihh' ⟩

    have hq: x = (GCD z.succ (x%z.succ))*k +z.succ*(x/z.succ) :=by{
      rw[← ihh']
      exact Eq.symm (Nat.mod_add_div x z.succ)
    }
    rcases ihh.left with ⟨ m, ihhl'⟩
    use  (x/z.succ) * m + k
    rw[Nat.mul_add]
    rw[Nat.mul_comm,  Nat.mul_assoc]
    rw[Nat.mul_comm m]
    rw[← ihhl']
    rw[Nat.mul_comm]
    rw[Nat.add_comm]
    have hz: z+1 = z.succ :=by omega
    rw[hz]
    omega
  }
  termination_by y
  decreasing_by {
      simp_wf
      apply Nat.mod_lt _
      refine Nat.zero_lt_of_ne_zero ?_
      tauto
  }

theorem gcd_is_greatest (x y: Nat):
  (x>0) → Not (∃ z: Nat, z∣ x ∧ z∣ y ∧ z> GCD x y ) := match y with
  | 0 => by {
    have hgcd0: GCD x 0 = x :=by {
      simp[GCD]
    }
    intro hx
    intro hh
    rcases hh with ⟨z0, hh' ⟩
    have hzx: z0 ≤ x :=by{
      have hzdx: z0∣ x:=by {tauto}
      rcases hzdx with ⟨k, hzdx'⟩
      have hk: k>0 :=by{
        contrapose hx
        have hk0: k=0 := by omega
        have hx0: x=0:= by simp[hzdx', hk0]
        omega
      }
      have hkg1: k>=1:=by{omega}
      rw[hzdx']
      have hz0: z0=z0*1:=by {omega}
      nth_rewrite 1 [hz0]
      exact Nat.mul_le_mul_left z0 hk
    }
    have: z0>GCD x 0:=by{tauto}
    rw[hgcd0] at this
    omega
  }
  | Nat.succ yy => by{
    intro hx
    intro hh
    rcases hh with ⟨z0, hh' ⟩
    have ih:=gcd_is_greatest yy.succ (x%yy.succ)
    have hyg0: yy.succ>0 :=by{omega}
    have ihh:= ih hyg0
    have hgcd: GCD x yy.succ = GCD yy.succ (x%yy.succ) := by {
      rw[GCD.eq_def]
      tauto
    }
    contrapose! ihh
    use z0
    have hzg: z0> GCD yy.succ (x%yy.succ):= by {
      omega
    }
    simp[hzg, hh']
    have hzx: z0∣ x:=by tauto
    rcases hzx with ⟨ k, hzx'⟩
    have hzy: z0 ∣ yy.succ :=by tauto
    rcases hzy with ⟨ m, hzy' ⟩
    have hmod:  x%yy.succ + yy.succ * (x/yy.succ) =x :=by{
      exact   Nat.mod_add_div x yy.succ
    }
    refine (Nat.dvd_mod_iff ?h.intro.intro.h).mpr ?h.intro.intro.a
    tauto
    tauto
  }
  termination_by y
  decreasing_by {
      simp_wf
      apply Nat.mod_lt _
      refine Nat.zero_lt_of_ne_zero ?_
      tauto
  }


def solveProg(t:Nat):Nat
:=
  let rec loop (i:{i':Nat//¬ ∃ i'' < i',i''*(i''+1)>=t*2}) (acc:{a:Nat//a*2=i.val*(i.val+1)})
  :{x:Nat//x*(x+1)>=t*2∧ ¬ ∃ y<x, y*(y+1)>=t*2}:=
    have ih:=acc.2
    have iih:=i.2
    if h:acc>=t then
      ⟨i, by constructor;omega;exact iih⟩
    else
      have hi: Not (i.val*(i.val+1)>=t*2):=by{
        rw[← ih]
        simp[h]
      }
      have: ¬∃ i'' < i.val + 1, i'' * (i'' + 1) ≥ t * 2:=by{
        simp
        intro x hx
        by_cases x < i.val
        next hlt=> simp at iih;  exact iih x hlt
        next hlt=>
          have : x=i:=by omega
          rw[this]
          simpa using hi
      }
      loop ⟨i.val+1,this⟩  ⟨acc.val+i.val+1, by ring_nf;rw[ih];ring⟩
    termination_by t-acc
    decreasing_by{
      simp_wf
      refine Nat.sub_lt_sub_left (by omega) (by omega)
    }
  loop ⟨ 0, by omega⟩  ⟨ 0, by simp⟩

theorem solveProg_isgeq(t:Nat): (solveProg t)*((solveProg t)+1) >= t*2
:=by
    simp[solveProg]
    have ih:=(solveProg.loop t ⟨ 0,by omega⟩  ⟨0, solveProg.proof_2⟩).2
    omega

theorem solveProg_ismin(t:Nat): Not (∃ y< (solveProg t), y*(y+1)>=t*2)
:=by
    simp[solveProg]
    have ih:=(solveProg.loop t ⟨ 0,by omega⟩  ⟨0, solveProg.proof_2⟩).2
    simp at ih
    exact ih.right


def solveGeom(a t:Nat)(h:a>1):Nat
:=
  let rec loop (h:a>1)(i:{i':Nat//¬ ∃i'' < i',a^(i''+1)-1>=t*(a-1)})(acc:{acc':Nat//a^(i.val+1)-1=acc'*(a-1)})
  :{x:Nat//a^(x+1)-1>=t*(a-1)∧ ¬∃ y<x,a^(y+1)-1>=t*(a-1)}:=
    have ih:=acc.2
    have iih:=i.2
    if hge:acc>=t then
      ⟨i, by rw [ih];constructor;exact Nat.mul_le_mul_right (a - 1) hge; exact iih⟩
    else
      let newacc:=acc+a^(i.val+1)
      have : a^(i.val+2)-1=newacc *(a-1):=by{
        ring_nf
        rw[← ih]
        ring_nf
        have : 0<  a * a ^ i.val :=by refine Nat.mul_pos (by omega) (by refine Nat.pow_pos (by omega))
        rw[← Nat.add_sub_assoc (by omega) (a * a ^ i.val * (a - 1))]
        ring_nf
        have: a * a ^ i.val+a * a ^ i.val * (a - 1)  =a * a ^ i.val*a:=by{
          have lem:=Nat.mul_one (a * a ^ i.val)
          nth_rewrite 1 [← lem]
          rw[← Nat.mul_add (a*a^i.val) 1]
          have: 1+(a-1)=a:=by omega
          rw[this]
        }
        rw[this]
        ring_nf
      }
      have hopt:¬∃ i'' < i.val + 1, a ^ (i'' + 1) - 1 ≥ t * (a - 1):=by{
        simp
        intro x xh
        by_cases x < i.val
        next hlt=> simp at iih; exact iih x hlt
        next hlt=>
          have hxi: x=i :=by omega
          simp at hge
          rw[hxi,ih]
          refine Nat.mul_lt_mul_of_pos_right hge (by simp[h])
      }
      loop h ⟨i.val+1, hopt⟩  ⟨newacc,this ⟩
    termination_by t-acc
    decreasing_by{
      simp_wf
      refine Nat.sub_lt_sub_left (by omega) ?_
      have: a^(i.val+1)>0 :=by{
        refine Nat.pow_pos (by omega)
      }
      omega
    }
  loop h ⟨0, by simp⟩  ⟨1, by ring_nf⟩

theorem solveGeom_isgeq(a t:Nat)(h:a>1): a^((solveGeom a t h)+1)-1 >=t*(a-1)
:=by
    simp[solveGeom]
    have:=(solveGeom.loop a t h h ⟨0, by simp⟩  ⟨1, by ring_nf⟩).2
    simp[this]

theorem solveGeom_ismin(a t:Nat)(h:a>1): Not (∃ y<solveGeom a t h, a^(y+1)-1>= t*(a-1))
:=by
    simp[solveGeom]
    have:=(solveGeom.loop a t h h ⟨0, by simp⟩  ⟨1, by ring_nf⟩).2.2
    simp at this
    exact this


def solveSquare(t:Nat): Nat
:=
  let rec loop (i:{i':Nat//¬ ∃ i'' < i', i''*i''>=t})
  :{x:Nat//x*x>=t∧ ¬ ∃ y<x, y*y>=t} :=
    have iih:=i.2
    if hcomp: i*i>=t then
      ⟨ i, by simp[hcomp];simp at iih;exact iih⟩
    else
      loop ⟨i+1,
            by{
                simp
                intro x hx
                by_cases x < i.val
                next hlt=> simp at iih; exact iih x hlt
                next hlt=>
                  have hxi: x=i.val :=by omega
                  rw[hxi]
                  omega
            }⟩
    termination_by t-i*i
    decreasing_by{
      simp_wf
      refine Nat.sub_lt_sub_left (by omega) (by ring_nf;omega)
    }
  loop ⟨0, by simp⟩

theorem solveSquare_isgeq(t:Nat): (solveSquare t)*(solveSquare t)>=t
:=by
    simp[solveSquare]
    have:=(solveSquare.loop t ⟨0, by simp⟩).2
    simp[this]

theorem solveSquare_ismin(t:Nat): Not (∃ y< (solveSquare t), y*y>=t)
:=by
    simp[solveSquare]
    have:=(solveSquare.loop t ⟨0, by simp⟩).2.2
    simp at this
    exact this

def f[Monad m] (op: Nat->Nat->(m Nat)) (n: Nat): (m Nat)
:=
  match n with
  | 0 => pure 1
  | 1 => pure 1
  | n + 2 =>
    do
      let x ← f op (n + 1)
      let y ← f op n
      op x y


theorem f_base (op : Nat → Nat → Id Nat) :
    (f op 0 = pure 1) ∧  (f op 1 = pure 1)
:= by constructor <;> rfl


theorem f_recursive (op : Nat → Nat → Id Nat) (n : Nat) : f op (n+2) =do {op (←  f op (n+1)) (←  f op n) }
:= by rfl

def rev(xs: List Int): List Int
:= match xs with
  |[] => []
  |h::t => (rev t) ++ [h]

theorem reverse_correct(xs:List Int):
  xs.length=(rev xs).length ∧
  ∀ i<xs.length, xs[i]! =(rev xs)[xs.length-1-i]!
  :=by{
    induction xs
    next=>simp[rev]
    next h t ih=>
    constructor
    · {
        simp[rev,ih]
    }
    · {
        simp[rev]
        intro i
        have hlen: (rev t).length=t.length:=by{
            simp [ih.left]
        }
        cases i with
        |zero=>
          simp
          have :t.length<(rev t ++[h]).length :=by{
            exact List.get_of_append_proof rfl hlen
          }
          have hind:(rev t ++ [h])[t.length]! =(rev t ++ [h])[t.length] :=by{
            exact getElem!_pos (rev t ++ [h]) t.length this
          }
          simp[hind]
          exact Eq.symm (List.getElem_concat_length (rev t) h t.length (id (Eq.symm hlen)) this)
        |succ i'=>
          simp
          have:= ih.right i'
          intro hi'
          simp[hi'] at this

          have hlind:t.length-1-i'=t.length - (i' + 1) :=by{
            omega
          }
          have hh: (rev t)[t.length - 1 - i']! =(rev t ++ [h])[t.length - (i' + 1)]! :=by{
            simp[hlind]
            have hlt:t.length - (i' + 1)<(rev t).length :=by{
              simp[hlen]
              omega
            }
            have hl':(rev t)[t.length - (i' + 1)]! =(rev t)[t.length - (i' + 1)] :=by{
              exact getElem!_pos (rev t) (t.length - (i' + 1)) hlt
            }
            have hrlen: (rev t ++ [h]).length>(rev t).length:=by {
              exact
                List.get_of_append_proof rfl rfl
            }
            have hrlt: t.length - (i' + 1)<(rev t ++ [h]).length :=by{
              omega
            }
            have hr': (rev t ++ [h])[t.length - (i' + 1)]! =(rev t ++ [h])[t.length - (i' + 1)] :=by{
              refine getElem!_pos (rev t ++[h]) (t.length - (i' + 1)) ?_

            }
            simp[hr',hl']
            refine Eq.symm (List.getElem_append_left (as:= rev t) (bs:=[h]) ?_)
            omega
          }
          omega


    }

  }


def maxProp(xs:List Int)(x:Int):=
  x∈ xs ∧∀ y∈ xs, x≥ y

def findMaxA (xs: List Int): Option <| Subtype <| maxProp xs :=
  match hm: xs.attach with
  |[]=>none
  |h::t=>

    let rec helper (curr: {y//y∈ xs})(rest:List {y//y∈ xs})
    :{y//y∈ xs ∧ ∀ y'∈ curr::rest, y'<=y}:=
      match rest with
      |[]=> ⟨curr, by simp[maxProp,curr.2]⟩
      |rh::rt=>
        let newmax:= if rh.val>curr.val then rh else curr
        let r:=helper newmax rt
        have ih:=r.2
        have ihr:=ih.right
        ⟨ r, by {
                simp[ih]

                have:=ihr newmax (by simp)
                have hgeq: newmax.val>=curr.val∧ newmax.val >=rh.val:=by{
                  simp[newmax]
                  split <;> constructor<;> try simp
                  next hsplit=> exact le_of_lt hsplit
                  next hsplit=>simp at hsplit; exact hsplit
                }
                constructor
                omega
                constructor
                omega
                intro a b hab
                have:=ihr ⟨ a,b⟩ (by simp[hab])
                simp[this]
        }⟩

    let res:=helper h t
    have ih:=res.2
    have ihr:=ih.right
    some ⟨ res, by {
                  simp[maxProp,ih]
                  intro y yh
                  let yy:{x//x∈xs}:=⟨ y,yh⟩
                  have hin:yy∈ h::t :=by{
                    rw[← hm]
                    exact List.mem_attach xs yy
                  }
                  have:= ihr yy hin
                  simp[this]
                  }⟩

def findMax (xs : List Int) : Option Int
:= match xs with
|[]=>none
|h::t=> findMaxA (h::t)


theorem findMax_correct(x: Int) (xs : List Int):
  ∃ max∈ (x::xs),
    And (findMax (x::xs) = some max) (∀ y ∈ (x::xs) , y ≤ max)
:=by
    simp only[findMax,pure]
    have hsome: findMaxA (x::xs)|>.isSome :=by exact rfl
    match hm: findMaxA (x::xs) with
    |none=>contradiction
    |some y=>
      use y
      simp
      have:=y.2
      simp[maxProp] at this
      exact this



theorem findMax_base : findMax [] = none
:=by
    unfold findMax
    simp only [findMaxA]

abbrev minSol(xs:List Int):=
  {x:Int//x∈xs ∧ ∀ y∈ xs, y>=x}

def findMinTyped (xs : List Int)
: {r:Option  (minSol xs) // r=none ↔ xs=[]}
:=match hm:xs with
|[]=> ⟨ none, by simp⟩
|h::t=>
  let rest:=findMinTyped t
  match hr: rest with
  |⟨ none, hn⟩  =>
    let sol:minSol (h::t) :=⟨ h, by simp[hm]; simp at hn; simp[hn] ⟩
    ⟨ some sol, by simp ⟩
  |⟨some r,_⟩  =>
    let newmin:{y:Int//y∈ h::t∧ y≤ h ∧ y≤ r}:=if hcomp:h<r then ⟨h,by simp;omega⟩  else ⟨r,by simp[r.2];omega⟩
    have ih:=r.2
    let sol:minSol (h::t):=
      ⟨ newmin,
      by constructor;exact newmin.2.left;simp[newmin.2];intro a ha;have:=ih.right a ha; omega
      ⟩
    ⟨ some sol, by simp⟩

def findMin (xs:List Int):Option Int
:=match xs with
|[]=>none
|h::t=>findMinTyped (h::t) |>.val

theorem findMin_correct(x: Int) (xs : List Int):
  ∃ min∈ (x::xs),
    And (findMin (x::xs) = some min) (∀ y ∈ (x::xs) , y >= min)
:=by
    simp only [findMin,pure]
    --have hsome: findMinTyped (x::xs)|>.val.isSome :=by sorry
    match hm: findMinTyped (x::xs) with
    |⟨ none, hn⟩ =>simp at hn
    |⟨ some y,_⟩ =>
      use y
      simp
      have :=y.2
      constructor;simpa using this.left;simpa using this.right

theorem findMin_base : findMin [] = none
:=by exact rfl

def isIn (x:Int) (xs: List Int):Bool
  := match xs with
  |[] => false
  |h::t => x==h || isIn x t

def isIn_correct (x:Int)(xs:List Int):
  isIn x xs = true ↔ x∈ xs := by{
    induction xs with
    |nil=> simp[isIn]
    |cons h t ih=> simp[isIn,ih]
  }


def countEq (x:Int)(xs:List Int):Nat
:= match xs with
  |[]=>0
  |h::t =>
    let c:= if h=x then 1 else 0
    (countEq x t) + c

def countEq_correct (x:Int)(xs:List Int):
  List.count x xs = countEq x xs
:=by{
    induction xs with
    |nil =>rfl
    |cons h t ih=>
      simp[countEq]
      have lem:=List.count_cons x h t
      rw[← ih]
      rw[lem]
      simp
  }

def findIfT(xs:List Int)(p:Int->Bool)
:{oi:Option Int//
if (∃ x∈ xs, p x) then ∃ y∈ xs, oi=some y ∧ p y
else oi=none}
:=match xs with
  |[]=>⟨ none, by exact rfl⟩
  |h::t=>
    if hp: (p h=true) then
      ⟨ some h, by simp[hp]⟩
    else
      let rest:=findIfT t p
      ⟨ rest, by simp[hp,rest.2]⟩

def findIf(xs:List Int)(p:Int->Bool):Option Int
:=findIfT xs p

theorem findIf_some(xs:List Int)(p:Int->Bool):
  (∃ x∈ xs, p x) -> ∃ y∈ xs, findIf xs p=some y ∧ p y
:=by
    simp only [findIf]
    have:=(findIfT xs p).2
    intro h
    simp[h] at this
    exact this


theorem findIf_none(xs:List Int)(p:Int->Bool):
  (¬ ∃ y∈ xs, p y =true)-> findIf xs p=none
:=by
    simp only [findIf]
    have:=(findIfT xs p).2
    intro h
    simp[h] at this
    exact this

def filterIf(xs:List Int)(p:Int->Bool):List Int
:=
  match xs with
  |[] => []
  |h::t =>
    if p h then
       h::(filterIf t p)
    else
      filterIf t p


theorem filterIf_correct(xs:List Int)(p:Int->Bool):
  filterIf xs p = List.filter p xs
:=by
    induction xs with
    |nil=> simp[filterIf]
    |cons h t ih=>
      simp[List.filter_cons]
      simp[filterIf]
      rw[ih]

def mapInt(xs:List Int)(f:Int->Int):List Int
:=match xs with
  |[]=>[]
  |h::t=> (f h) :: (mapInt t f)

theorem mapInt_correct(xs:List Int)(f:Int->Int)
: (mapInt xs f).length=xs.length
∧  ∀ i:Fin xs.length, (mapInt xs f)[i]! = f xs[i]
:=by
    induction xs with
    |nil=>simp[mapInt]
    |cons h t ih=>
      have hsize:(mapInt (h :: t) f).length = (h :: t).length :=by{
        simp[mapInt,ih]
      }
      constructor
      · exact hsize
      · {
        intro i
        have hil:i<(mapInt (h :: t) f).length :=by{
          simp[hsize]
        }
        have: (mapInt (h :: t) f)[i]! =(mapInt (h :: t) f)[i] :=by{
          exact getElem!_pos (mapInt (h :: t) f) i hil
        }
        rw[this]
        rcases i with ⟨i',hi⟩
        cases i'
        next=>
          simp[mapInt]

        next n=>
          simp[mapInt]
          have:=ih.right ⟨ n,by simp at hi;exact hi⟩
          simp at this
          rw[← this]
          symm
          exact getElem!_pos (mapInt t f) n (by simp at hi; omega)

      }

def isPrefix (p xs:List α):=
  List.take p.length xs = p

/- longest common prefix for a pair of lists-/
def lcpPair(xs ys:List Int )
:{zs:List Int//isPrefix zs xs∧ isPrefix zs ys
   ∧ (∀zz, isPrefix zz xs∧ isPrefix zz ys->zz.length<=zs.length)}
:=match xs,ys with
  |[],_=>⟨ [],by simp[isPrefix]⟩
  |_,[]=>⟨ [],by simp[isPrefix]⟩
  |xh::xt, yh::yt=>
    if heq: xh=yh then
      let rest:=lcpPair xt yt
      ⟨ xh:: rest,
        by{
          have:=rest.2
          constructor
          ·  simpa[isPrefix,rest,heq] using this.1
          · {
            constructor
            · simpa[isPrefix,rest,heq] using this.2.1
            ·{
              intros zz hxy
              cases zz
              next=>
                have: ([]:List Int).length=0:=by exact rfl
                rw[this]
                omega
              next h t=>
                simp[isPrefix] at hxy
                have ih:=this.2.2
                have ht:isPrefix t xt∧ isPrefix t yt:=by {
                  simp[isPrefix,hxy]
                }
                have ihh:=ih _ ht
                simp[ihh]
            }
          }

        }
      ⟩
    else
      ⟨ [],
        by {
          simp[isPrefix]
          intros zz hx hy
          cases zz
          next=>rfl
          next h t=>
            simp at hx
            simp at hy
            have : xh=yh :=by simp[hx,hy]
            contradiction
        }
      ⟩
