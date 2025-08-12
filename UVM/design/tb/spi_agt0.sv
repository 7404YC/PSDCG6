class spi_agt extends uvm_agent;
  `uvm_component_utils(spi_agt)

  uvm_analysis_export #(spi_tran) agt0_ap;

  spi_drv drv;
  spi_mon mon;
  spi_sqr sqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    agt0_ap = new("agt0_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon0 = spi_mon::type_id::create("mon0", this);
    // Only create driver and sequencer if agent is active
    if (get_is_active() == UVM_ACTIVE) begin
      drv = spi_drv::type_id::create("drv", this);
      sqr = spi_sqr::type_id::create("sqr", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor's analysis port to agent's analysis port
    mon.mon0_ap.connect(agt0_ap);
    // Connect driver to sequencer if agent active
    if (get_is_active() == UVM_ACTIVE) begin
      drv.seq_item_port.connect(sqr.seq_item_export);
    end
  endfunction
endclass
