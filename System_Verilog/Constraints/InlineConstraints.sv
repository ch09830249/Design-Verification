/*
  By using the "with" construct, users can declare in-line constraints at the point where the randomize() method is called. 
  These additional constraints will be considered along with the object's original constraints by the solver.   // 匿名 constraints
*/

class Item;
  rand bit [7:0] id;

  constraint c_id { id < 25; }

endclass

module tb;

  initial begin
    Item itm = new ();
    itm.randomize() with { id == 10; }; 		// In-line constraint using with construct
    $display ("Item Id = %0d", itm.id);
  end
endmodule

/*
  # KERNEL: Item Id = 10
*/


class Item;
  rand bit [7:0] id;

  constraint c_id { id == 25; }
endclass

module tb;
  initial begin
    Item itm = new ();
    if (! itm.randomize() with { id < 10; })    // 和 id == 25 衝突
    	$display ("Randomization failed");
    $display ("Item Id = %0d", itm.id);
  end
endmodule

/*
      if (! itm.randomize() with { id < 10; })
                        |
  ncsim: *W,SVRNDF (./testbench.sv,10|22): The randomize method call failed.
  Observed simulation time : 0 FS + 0
  ncsim: *W,RNDOCS: These constraints contribute to the set of conflicting constraints:

    constraint c_id { id == 25; }; (./testbench.sv,4)
      if (! itm.randomize() with { id < 10; }) (./testbench.sv,10)
  ncsim: *W,RNDOCS: These variables contribute to the set of conflicting constraints:

  rand variables:
        id [./testbench.sv, 2]

  Randomization failed    => 有印出來
  Item Id = 0
*/


...
if (! itm.randomize() with { id == 10; })
...

/*
      if (! itm.randomize() with { id == 10; })
                        |
  ncsim: *W,SVRNDF (./testbench.sv,10|22): The randomize method call failed.
  Observed simulation time : 0 FS + 0
  ncsim: *W,RNDOCS: These constraints contribute to the set of conflicting constraints:

    constraint c_id { id == 25; }; (./testbench.sv,4)
      if (! itm.randomize() with { id == 10; }) (./testbench.sv,10)
  ncsim: *W,RNDOCS: These variables contribute to the set of conflicting constraints:

  rand variables:
        id [./testbench.sv, 2]

  Randomization failed    => 有印出來
  Item Id = 0
*/