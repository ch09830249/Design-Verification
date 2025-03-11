/*
    The SystemVerilog constraint solver by default tries to give a uniform distribution of random values. 
    Hence the probability of any legal value of being a solution to a given constraint is the same.
    But the use of solve - before can change the distribution of probability such that 
    certain corner cases can be forced to be chosen more often than others. 
    We'll see the effect of solve - before by comparing an example with and without the use of this construct.
*/

// Without solve-before => 就是先把所有合法的數組列出來, 再隨機挑選任一數組
class ABC;
  rand  bit			a;
  rand  bit [1:0] 	b;
  constraint c_ab { a -> b == 3'h3; }       // 當 a == 1, b 則為 3
endclass

module tb;
  initial begin
    ABC abc = new;
    for (int i = 0; i < 8; i++) begin
      abc.randomize();
      $display ("a=%0d b=%0d", abc.a, abc.b);
    end
  end
endmodule

/*
    a=0 b=0
    a=0 b=1
    a=0 b=0
    a=0 b=1
    a=0 b=2
    a=1 b=3 V
    a=0 b=3
    a=0 b=3
*/

/*
    a	b	Probability             總共有 5 種可能, 隨機挑一組 (機率皆相同)
    0	0	1/(1 + 2^2)
    0	1	1/(1 + 2^2)
    0	2	1/(1 + 2^2)
    0	3	1/(1 + 2^2)
    1	3	1/(1 + 2^2)             1 代表 (1, 3) 這組, 2^2 代表 0 和 b 的所有可能的搭配
*/



// With solve-before        先挑 solve 要挑的數, 再根據 solve 挑完的數, 決定 before 的數
class ABC;
  rand  bit			a;
  rand  bit [1:0] 	b;

  constraint c_ab { a -> b == 3'h3;

                    // Tells the solver that "a" has
                    // to be solved before attempting "b"
                    // Hence value of "a" determines value
                    // of "b" here
                  	solve a before b;
                  }
endclass

module tb;
  initial begin
    ABC abc = new;
    for (int i = 0; i < 8; i++) begin
      abc.randomize();
      $display ("a=%0d b=%0d", abc.a, abc.b);
    end
  end
endmodule

/*
    a=1 b=3
    a=1 b=3
    a=0 b=1
    a=0 b=0
    a=0 b=0
    a=0 b=1
    a=1 b=3
    a=0 b=2
*/

/*
    a	b	Probability
    0	0	1/2 * 1/2^2
    0	1	1/2 * 1/2^2
    0	2	1/2 * 1/2^2
    0	3	1/2 * 1/2^2
    1	3	1/2             挑到 a 的機率為 1/2, a 決定好了, b 只能挑 3, 故 1/2*1
*/


/*
  Restriction
    randc variables are not allowed since they are always solved first
    Variables should be integral values
    There should not be circular dependency in the ordering such as solve a before b combined with solve b before a.
*/