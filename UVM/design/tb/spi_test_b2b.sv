class spi_test_b2b extends spi_test;

	`uvm_component_utils(spi_test_b2b)

	spi_seq_b2b seq;

	function new (string name, uvm_component parent);
		super.new(name, parent);
		this.seq_count = 100;
	endfunction
	
  	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq = spi_seq_b2b::type_id::create("seq", this);
	endfunction

  	task run_phase(uvm_phase phase);

  	  	seq.seq_count = this.seq_count;
		seq.min_delay = 0;
		seq.max_delay = 0;

  	  	`uvm_info("TEST", $sformatf("Starting sequences with config: count=%0d", seq.seq_count), UVM_MEDIUM)

  	  	phase.raise_objection(this);
  	  	fork
  	  	  seq.start(env.agt0.sqr);
  	  	join

		#1000; // TODO: need indicator from scoreboard for drop_objection

  	  	phase.drop_objection(this);

  	endtask

endclass
