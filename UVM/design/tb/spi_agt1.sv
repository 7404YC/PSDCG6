class spi_agt1 extends uvm_agent;
  `uvm_component_utils(spi_agt1)

  uvm_analysis_export #(spi_tran) agt1_ap;

  spi_mon1 mon1;
  spi_mon2 mon2;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    agt1_ap = new("agt1_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon1 = spi_mon1::type_id::create("mon1", this);
    mon2 = spi_mon2::type_id::create("mon2", this);
    // Only create driver and sequencer if agent is active
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor's analysis port to agent's analysis port (1 to many)
    mon1.mon1_ap.connect(agt1_ap);
    mon2.mon2_ap.connect(agt1_ap);
  endfunction
endclass

