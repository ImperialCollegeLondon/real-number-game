import data.real.basic

notation `|` x `|` := abs x -- hide
notation `[` a `,` b `]`  := set.Icc a b
constant A : set.Icc (3:ℝ) 5
constant B : [(3:ℝ), 5]
#check A
#check B
variable X : [(3:ℝ), 5]
variable Y : set.Icc (3:ℝ) 5
#check X
#check Y
#check |(3:ℝ)|