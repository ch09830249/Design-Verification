module tb;

  // This initial block has a forever loop which will "run forever"
  // Hence this block will never finish in simulation
  initial begin
    forever begin // like while(1)
      #5 $display ("Hello World !");
    end
  end

  // Because the other initial block will run forever, our simulation will hang!
  // To avoid that, we will explicity terminate simulation after 50ns using $finish
  initial begin
    #50 $finish;
  end
endmodule