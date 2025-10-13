use crate::ff::FiniteField;

pub fn xgcd(x: u64, y: u64) -> (i128, i128, i128) {
    if y == 0 {
      return (x as i128, 1, 0);
    }
    
    let (gcd, x1, y1) = xgcd(y, x % y);
    let x2 = y1;
    let y2 = x1 - (x as i128 / y as i128) * (y1 as i128);
    
    (gcd, x2, y2)
  }