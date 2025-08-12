class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

	int seq_count = 10;
	int seq_index = 0;
	string seq_type = "normal";
	int max_delay = 0;
	int min_delay = 0;
	int delay;

	event spi_done_event;

	function new(string name = "spi_seq");
  	  super.new(name);
  	endfunction

	function int get_random_delay();
		return $urandom_range(min_delay, max_delay);
	endfunction

	virtual task body();

		spi_tran tr;
		`uvm_info(get_type_name(), "Normal Priority Sequence", UVM_MEDIUM)
		
		for (int i=0; i<this.seq_count; i++) begin

			tr = spi_tran::type_id::create("tr");
			start_item(tr);

			assert(tr.randomize() with {rst_n == 1; });

			delay = get_random_delay();
			seq_index++;
			tr.seq_count = this.seq_count;
			tr.seq_index = this.seq_index;
			tr.seq_type = this.seq_type;
			
			#(delay);
			finish_item(tr);

			`uvm_info(get_type_name(),
				$sformatf("Sent %0d/%0d %s sequence: %0b Next sequence after",
					this.seq_index, this.seq_count, this.seq_type, 0),
				UVM_MEDIUM)

			// Wait for spi_done_event trigger
			@(spi_done_event);

		end

	endtask

endclass

