Function  
Cannot have time-controlling statements/delay, and hence executes in the same simulation time unit  
Cannot enable a task, because of the above rule  
Should have atleast one input argument and cannot have output or inout arguments  
Can return only a single value  
  
Task  
Can contain time-controlling statements/delay and may only complete at some other time  
Can enable other tasks and functions  
Can have zero or more arguments of any type  
Cannot return a value, but can achieve the same effect using output arguments  
