class ABC;
  string fruit;

  // Note that the constructor is defined as "virtual" which is not allowed
  // in SystemVerilog. Class constructor cannot be "static" either
  virtual function new ();
    fruit = "Apple";
  endfunction

endclass

// Instantiate the class object and print its contents
module tb;
  	initial begin
      ABC abc = new();
      $display ("fruit = %s", abc.fruit);
    end
endmodule

/*
  fruit = Apple
*/