module
public import LogTwoCheckpoints.Part035
@[expose] public section
set_option Elab.async false

example : LogTwo.irrationalityExponent (Real.log 2) = 2 :=
  LogTwo.irrationalityExponent_log_two
#print axioms LogTwo.irrationalityExponent_log_two
