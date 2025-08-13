class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

	int seq_count = 10;
	int seq_index = 0;
	string seq_type = "normal";
	int max_delay = 0;
	int min_delay = 0;
	int delay;

	function new(string name = "spi_seq");
  	  super.new(name);
  	endfunction

	function int get_random_delay();
		return $urandom_range(min_delay, max_delay);
	endfunction

	function void update_seq_info(ref spi_tran tr);
		tr.seq_count = this.seq_count;
		tr.seq_index = this.seq_index;
		tr.seq_type = this.seq_type;
	endfunction

endclass

