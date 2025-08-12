class spi_env extends uvm_env;
  `uvm_component_utils(spi_env)

  spi_agt0 agt0;
  spi_agt1 agt1;
  
  // TODO: YK to enable later
  //spi_scb scb;
  //spi_cov cov;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
	// Set agent as active
	uvm_config_db#(uvm_active_passive_enum)::set(this, "agt0", "is_active", UVM_ACTIVE);
	uvm_config_db#(uvm_active_passive_enum)::set(this, "agt1", "is_active", UVM_PASSIVE);
    agt0 = spi_agt0::type_id::create("agt0", this);
    agt1 = spi_agt1::type_id::create("agt1", this);

	// TODO: YK to enable later
    //scb = spi_scb::type_id::create("scb", this);
    //cov = spi_cov::type_id::create("cov", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
	// TODO: YK to enable later
    //agt.agt_ap.connect(scb.scb_imp);
    //agt.agt_ap.connect(cov.cov_imp);
  endfunction
endclass
