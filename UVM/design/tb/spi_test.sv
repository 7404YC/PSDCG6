class spi_test extends uvm_test;
  `uvm_component_utils(spi_test)

	spi_env env;
  	spi_seq seq;

	uvm_event spi_done_event;

	int seq_count = 2;

  	function new(string name, uvm_component parent);
		super.new(name, parent);
  	endfunction

  	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
  	  	env = spi_env::type_id::create("env", this);
		seq = spi_seq::type_id::create("seq", this);
  	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);

		spi_done_event = env.agt1.mon1.spi_done_event;
		seq.spi_done_event = spi_done_event;
	endfunction

  	task run_phase(uvm_phase phase);

  	  	seq.seq_count = this.seq_count;

  	  	`uvm_info("TEST", $sformatf("Starting sequences with config: Normal: count=%0d", seq.seq_count), UVM_MEDIUM)

  	  	phase.raise_objection(this);
  	  	fork
  	  	  seq.start(env.agt0.sqr);
  	  	join

  	  	phase.drop_objection(this);

  	endtask
endclass
