use creusot_contracts::*;
use crate::two_state::two_state::{PreOrd, TwoState, TwoStateToken};
use crate::two_state::two_state_cell::TwoStateCell;

#[ensures(result.id() == cell.id() && result.value() >= val)]
fn test_cell_max(cell: &TwoStateCell<u32>, val: u32) -> TwoStateToken<u32> {
    let mut ts = cell.take();
    let tok = ts.update( #[ensures(^v >= *v && ^v >= val)] |v| {
        if val > *v {
            *v = val;
        }
    });
    cell.put_back(ts);
    tok
}

#[requires(tok.id() == cell.id())]
#[ensures(result >= tok.value())]
fn test_cell_get(cell: &TwoStateCell<u32>, tok: TwoStateToken<u32>) -> u32 {
    let ts = cell.take();
    ts.check_token(tok);
    let v = *ts.get();
    cell.put_back(ts);
    v
}

impl<T: DeepModel> PreOrd for T
    where T::DeepModelTy: OrdLogic {
    #[logic]
    fn le(self: T, oth: T) -> bool {
        self.deep_model().le_log(oth.deep_model())
    }

    #[law]
    #[ensures(self.le(self))]
    fn refl(self) {}

    #[law]
    #[ensures(self.le(mid) ==> mid.le(end) ==> self.le(end))]
    fn trans(self, mid: Self, end: Self) {}
}


fn test1() {
    let (mut x, tok1) = TwoState::new_with_token(5);
    let tok2 = x.update(#[requires(*x == 5u32)] #[ensures(^x == 7u32)] |x| *x += 2 );
    proof_assert!(x.id() == tok1.id());
    proof_assert!(tok2.value() == 7u32)
}

#[requires(x.id() == tok.id())]
#[ensures(x.value() >= tok.value())]
fn test2(x: &TwoState<u32>, tok: TwoStateToken<u32>) {
    x.check_token(tok)
}



impl<'a> PreOrd for &'a mut Bad<'a> {
    #[logic]
    fn le(self, oth: Self) -> bool {
        true
    }

    #[law]
    #[ensures(self.le(self))]
    fn refl(self) {}

    #[law]
    #[ensures(self.le(mid) ==> mid.le(end) ==> self.le(end))]
    fn trans(self, mid: Self, end: Self) {}
}

enum Bad<'a> {
    None,
    Some(Ghost<&'a mut Bad<'a>>)
}

fn test_bad() {
    let mut x = Bad::None;
    let m = &mut x;
    let g = ghost!(m);
    *m = Bad::Some(ghost!(*g));
    proof_assert!(*m == Bad::Some(g));
    proof_assert!(^(*g) == ^m);
    let _ = m;
    proof_assert!(^(*g) == Bad::Some(g));
}