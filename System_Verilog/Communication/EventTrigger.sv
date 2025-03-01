/*
  An event's triggered state persists throughout the time step, until simulation advances. 
  Hence if both wait for the event and trigger of the event happens at the same time 
  there will be a race condition and the triggered property helps to avoid that.
*/

// A process that waits on the triggered state always unblocks, regardless of the order of wait and trigger.
module tb;

  // Create an event variable that processes can use to trigger and wait
  event event_a;

  // Thread1: Triggers the event using "->" operator at 20ns
  initial begin
    #20 ->event_a;
    $display ("[%0t] Thread1: triggered event_a", $time);
  end

  // Thread2: Starts waiting for the event using "@" operator at 20ns
  initial begin
    $display ("[%0t] Thread2: waiting for trigger ", $time);
    #20 @(event_a);
    $display ("[%0t] Thread2: received event_a trigger ", $time);
  end

  // Thread3: Starts waiting for the event using ".triggered" at 20ns
  initial begin
    $display ("[%0t] Thread3: waiting for trigger ", $time);
    #20 wait(event_a.triggered);
    $display ("[%0t] Thread3: received event_a trigger", $time);
  end
endmodule

/*
  [0] Thread2: waiting for trigger 
  [0] Thread3: waiting for trigger 
  [20] Thread1: triggered event_a
  [20] Thread3: received event_a trigger
*/