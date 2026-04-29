class axi_scoreboard extends uvm_component;
  `uvm_component_utils(axi_scoreboard)
  uvm_tlm_analysis_fifo #(axi_txn) fifo;


  function new(string name = "axi_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    fifo = new("fifo", this);
  endfunction


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    axi_txn tr;
    forever begin
      fifo.get(tr);
      `uvm_info(get_type_name(),
        $sformatf("Scoreboard got txn:\n%s", tr.sprint()),
        UVM_LOW)
    end
  endtask


endclass
