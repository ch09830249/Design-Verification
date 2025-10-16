`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_seq_item extends uvm_sequence_item;
  rand bit en;

  `uvm_object_utils(counter_seq_item)

  function new(string name="counter_seq_item");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("en=%0b", en);
  endfunction

endclass