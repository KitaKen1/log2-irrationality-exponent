module
public import LogTwo.Target
@[expose] public section
-- The FC target uses only the independent project definition.
example : LogTwo.irrationalityExponent (Real.log 2) = 2 :=
  LogTwo.irrationalityExponent_log_two
#print axioms LogTwo.irrationalityExponent_log_two
