module tb;

  // Create event variables
  event event_a, event_b;

  initial begin
    fork
      // Thread1: waits for event_a to be triggered
      begin
        @(event_a);
        // wait(event_a.triggered);
        $display ("[%0t] Thread1: Wait for event_a is over", $time);
      end

  	  // Thread2: waits for event_b to be triggered
      begin
        @(event_b);
        // wait(event_b.triggered);
        $display ("[%0t] Thread2: Wait for event_b is over", $time);
      end

      // Thread3: triggers event_a at 20ns
      #20 ->event_a;

      // Thread4: triggers event_b at 30ns
      #30 ->event_b;

      // Thread5: Assigns event_b to event_a at 10ns
      begin
        // Comment code below and try again to see Thread2 finish later
        #10 event_b = event_a;
      end
    join
  end
endmodule

/*
  [20] Thread1: Wait for event_a is over
  [20] Thread2: Wait for event_b is over
*/