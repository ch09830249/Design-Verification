module tb_top;
   bit [7:0] array [8];   // Create a fixed size array

   initial begin

      // Assign a value to each location in the array
      foreach (array [index]) begin
         array[index] = index;
      end

      // Iterate through each location and print the value of current location
      foreach (array [index]) begin
         $display ("array[%0d] = 0x%0d", index, array[index]);
      end
   end
endmodule