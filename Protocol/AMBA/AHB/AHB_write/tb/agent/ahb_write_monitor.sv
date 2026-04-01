class ahb_write_monitor extends uvm_monitor;
  `uvm_component_utils(ahb_write_monitor)

  virtual ahb_if vif;

  uvm_analysis_port #(ahb_transaction) ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.HCLK);
      if (vif.HTRANS == 2'b10 && !vif.HWRITE && vif.HREADY) begin
        ahb_transaction tr = ahb_transaction::type_id::create("tr");
        `uvm_info(get_type_name(), "Monitor write data", UVM_MEDIUM)
        tr.addr = vif.HADDR;
        tr.data = vif.HRDATA;
        tr.size = vif.HSIZE;
        tr.print();
        ap.write(tr);
      end
    end
  endtask
endclass

