class spi_seq_sanity extends spi_seq;

	`uvm_object_utils(spi_seq_sanity)

	function new (string name="spi_seq_sanity");
		super.new(name);
	endfunction

	virtual task body();

		spi_tran tr;

		for (int i=0; i<this.seq_count; i++) begin
			
			tr = spi_tran::type_id::create("tr");

			start_item(tr);

			assert(tr.randomize() with {start == 1;});
			tr.rst_n = 1;

			delay = get_random_delay();
			seq_index++;
			update_seq_info(tr);

			`uvm_info(get_type_name(),
				$sformatf("Sent %0d/%0d %s sequence: rst_n=%0b, start=%0b, tx_data=0x%0h",
					this.seq_index, this.seq_count, this.seq_type, tr.rst_n, tr.start, tr.tx_data),
				UVM_MEDIUM)

			#(delay);
			finish_item(tr);

		end

	endtask

endclass
