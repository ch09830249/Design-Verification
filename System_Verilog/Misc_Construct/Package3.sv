// Nested Package
// Define a new package called X
package X;
  byte    lb     = 8'h10;
  int     word   = 32'hcafe_face;
  string  name = "X";

  function void display();
    $display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);
  endfunction
endpackage

// Define a new package called Y, use variable value inside X within Y
package Y;
  import X::*;      // 引入另一個 pkg

  byte    lb   = 8'h10 + X::lb;
  string  name = "Y";

  function void display();
    $display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);
  endfunction
endpackage

// Define a new package called Z, use variable value inside Y within Z
package Z;
  import Y::*;

  byte    lb   = 8'h10 + Y::lb;
  string  name = "Z";

  function void display();
    // Note that 'word' exists in package X and not in Y, but X
    // is not directly imported here in Z, so the statement below
    // will result in a compilation error
    //$display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);  // ERROR !

    $display("pkg=%s lb=0x%0h", name, lb);
  endfunction
endpackage

module tb;
  // import only Z package
  import Z::*;

  initial begin
    X::display();   // Direct reference X package
    Y::display();   // Direct reference Y package
    display();      // Taken from Z package because of import
  end
endmodule

/*
    Top level design units:
      X
      Y
      Z
      tb
  Loading snapshot worklib.tb:sv .................... Done
  ...
  xcelium> run
  pkg=X lb=0x10 word=0xcafeface                     呼叫該 pkg 的 method, 且印出該 pkg 的變數
  pkg=Y lb=0x20 word=0xcafeface
  pkg=Z lb=0x30
  xmsim: *W,RNQUIE: Simulation is complete.
*/