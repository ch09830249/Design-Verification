class axi_coverage extends uvm_subscriber #(axi_txn);
    `uvm_component_utils(axi_coverage)

    covergroup cov;
        burst_cp: coverpoint trans.burst_type;
        size_cp:  coverpoint trans.burst_size;
        qos_cp:   coverpoint trans.qos;
    endgroup

    axi_txn trans;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        cov = new();
    endfunction

    function void write(axi_txn t);
        this.trans = t;
        cov.sample();
    endfunction
endclass
