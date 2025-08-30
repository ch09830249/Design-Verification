class axi_read_monitor extends uvm_monitor;
  `uvm_component_utils(axi_read_monitor)

  virtual axi_read_if vif;
  uvm_analysis_port #(axi_read_transaction) ap;

  function new(string name = "axi_read_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual axi_read_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(), "Virtual interface not found!")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);

    axi_read_transaction tr;

    forever begin
      @(posedge vif.ACLK);
      if (vif.ARVALID && vif.ARREADY) begin                   // 當 ARVALID && ARREADY 舉起, Read address 已經送出
        tr = axi_read_transaction::type_id::create("tr");
        tr.araddr = vif.ARADDR;
      end

      if (vif.RVALID && vif.RREADY) begin                     // 當 RVALID && RREADY 舉起, Read data 已經收到
        if (tr == null) tr = axi_read_transaction::type_id::create("tr");
        tr.rdata = vif.RDATA;
        tr.rresp = vif.RRESP;
        `uvm_info(get_type_name(), "Monitor read data", UVM_MEDIUM)
        tr.print();
        ap.write(tr);     // 這是要送給 scoreboard 去比對用
      end
    end

  endtask
endclass
