module tb;
  // Declare three events that can be triggered separately
  event a, b, c;

  // This block triggers each event one by one
  initial begin
    #10 -> a;
    #10 -> b;
    #10 -> c;
  end

  // This block waits until each event is triggered in the given order
  initial begin
    wait_order (a,b,c)
      $display ("Events were executed in the correct order");
    else
      $display ("Events were NOT executed in the correct order !");
  end
endmodule

/*
  Events were executed in the correct order
*/