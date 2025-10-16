`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_scoreboard extends uvm_component;
  uvm_analysis_imp #(counter_seq_item, counter_scoreboard) imp;
  virtual counter_if vif;
  logic [3:0] exp_count;

  `uvm_component_utils(counter_scoreboard)

  function new(string name="counter_scoreboard", uvm_component parent=null);
    super.new(name, parent);
    imp = new("imp", this);
    exp_count = 0;
  endfunction

  function void write(counter_seq_item t);
    // Step1: 先比對當前 DUT 的輸出 (和上一拍計算的 exp_count)
    if (vif.count !== exp_count)
      `uvm_error("SCOREBOARD", $sformatf("Mismatch! exp=%0d, got=%0d", exp_count, vif.count))
    else
      `uvm_info("SCOREBOARD", $sformatf("PASS exp=%0d, got=%0d", exp_count, vif.count), UVM_LOW)

    // Step2: 再更新下一拍的期望值
    if (vif.rst_n == 0)
      exp_count = 0;
    else if (t.en)
      exp_count = (exp_count + 1) % 16; // wrap-around
  endfunction

endclass