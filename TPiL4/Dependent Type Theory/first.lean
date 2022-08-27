namespace BasicFunctions
#eval 2+2

def sampleFunc (x : Nat) := x*x + 3
#eval sampleFunc (2)

def result := sampleFunc 3
#eval println! "The result of sample function is {result}"

def condFunc (x : Nat) := 
  if x > 100 then
    "High"
  else
    "Low"

#eval condFunc 120

end BasicFunctions