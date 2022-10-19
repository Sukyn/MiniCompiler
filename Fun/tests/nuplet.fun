let x = true in
let t = (2, 5, if x then 7 else 8, 9) in
t[0] * (t[0] + t[1])
