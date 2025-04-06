/*
The normal constraints are called hard constraints because it is mandatory for the solver to always satisfy them. 
If the solver fails to find a solution, then the randomization will fail.

However, a constraint declared as soft gives the solver some flexibility that 
the constraint need to be satisfied if there are other contradicting constraints - 
either hard or a soft constraint with higher priority.      會有 soft constraint 存在, 就是其他 constraints 可能 priority 比較高

Soft constraints are used to specify default valus and distributions for random variables.s
*/

class ABC;
  rand bit [3:0] data;

  // This constraint is defined as "soft"
  constraint c_data { soft data >= 4;     // 多了 soft 4~12
                           data <= 12; }
endclass

module tb;
  ABC abc;

  initial begin
    abc = new;
    for (int i = 0; i < 5; i++) begin
      abc.randomize();
      $display ("abc = 0x%0h", abc.data);
    end
  end
endmodule

/*
  abc = 0x4
  abc = 0x8
  abc = 0x4
  abc = 0x7
  abc = 0x7
*/


module tb;
  ABC abc;

  initial begin
    abc = new;
    for (int i = 0; i < 5; i++) begin
      abc.randomize() with { data == 2; };    // 此 inline constraint 為 hard
      $display ("abc = 0x%0h", abc.data);
    end
  end
endmodule

/*
  abc = 0x2
  abc = 0x2
  abc = 0x2
  abc = 0x2
  abc = 0x2
*/