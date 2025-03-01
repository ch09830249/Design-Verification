module tb;

  initial display();

  initial begin
  	// After 50 time units, disable a particular named
  	// block T_DISPLAY inside the task called 'display'
    #50 disable display.T_DISPLAY;
  end

  task display();
    begin : T_DISPLAY
      $display("[%0t] T_Task started", $time);
      #100;
      $display("[%0t] T_Task ended", $time);
    end

    begin : S_DISPLAY
      #10;
      $display("[%0t] S_Task started", $time);
      #20;
      $display("[%0t] S_Task ended", $time);
    end
  endtask
endmodule

/*
  [0] T_Task started  => 只有停掉 T_DISPLAY 這個 block
  [60] S_Task started => 50 停掉 T_DISPLAY 這個 block, 開始執行 S_DISPLAY block
  [80] S_Task ended
*/