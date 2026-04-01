`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_sequence extends uvm_sequence #(counter_seq_item);

  `uvm_object_utils(counter_sequence)

  function new(string name="counter_sequence");
    super.new(name);
  endfunction

  task body();
    counter_seq_item req;
    repeat (20) begin
      req = counter_seq_item::type_id::create("req");
      assert(req.randomize());
      `uvm_info("SEQ", $sformatf("Generated: %s", req.convert2string()), UVM_MEDIUM)
      start_item(req);
      finish_item(req);
    end
  endtask

endclass