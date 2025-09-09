class ahb_read_monitor extends uvm_component;
  `uvm_component_utils(ahb_read_monitor)

  virtual ahb_if vif;
  uvm_analysis_port #(ahb_transaction) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction

  task run_phase(uvm_phase phase);
  ahb_transaction tr;
    forever begin
      @(posedge vif.HCLK);
      if (vif.HTRANS == 2'b10 && !vif.HWRITE && vif.HREADY) begin
        tr = ahb_transaction::type_id::create("tr");
        tr.addr = vif.HADDR;
        tr.size = vif.HSIZE;
        tr.data = vif.HRDATA;
        `uvm_info("ahb_read_monitor", "Monitor read data", UVM_MEDIUM)
        tr.print();
        mon_ap.write(tr);
      end
    end
  endtask
endclass
