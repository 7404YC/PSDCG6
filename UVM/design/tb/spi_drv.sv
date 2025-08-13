class spi_drv extends uvm_driver #(spi_tran);

	`uvm_component_utils(spi_drv)

	uvm_analysis_port # (spi_tran) drv_ap = new("drv_ap", this);

	virtual spi_if vif;

	int min_hold_delay = 1, max_hold_delay = 33;

	function new(name, uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db # (virtual spi_if)::get(this, "", "vif", vif)) begin
			`uvm_error("DRIVER", "Virtual interface (drv_cb) not found in config db")
		end
	endfunction

	task run_phase(uvm_phase phase);

		spi_tran tr;
		int hold_cycles;

		repeat (2) @(vif.drv_cb);
		vif.rst_n = 1;

		forever begin

			@ (vif.drv_cb);

			// driver connects the signals 
			seq_item_port.get_next_item(tr);
			vif.start = tr.start;
			vif.rst_n = tr.rst_n;
			vif.tx_data = tr.tx_data;

			hold_cycles = $urandom_range(min_hold_delay, max_hold_delay);

			// driver write to ap for scoreboard record
			drv_ap.write(tr);
			seq_item_port.item_done();

			`uvm_info(get_type_name(),
				$sformatf("Drive %0d/%0d transaction to DUT: rst_n=%0b, start=%0b, tx_data=0x%0h",
					tr.seq_index, tr.seq_count, tr.rst_n, tr.start, tr.tx_data),
				UVM_MEDIUM)

			fork
				begin
					repeat (hold_cycles) @(vif.drv_cb);
					vif.start = 1'b0;

					`uvm_info(get_type_name(),
					$sformatf("For %0d/%0d transaction to DUT: after %0d delay, drive rst_n=%0b, start=%0b, tx_data=0x%0h",
						tr.seq_index, tr.seq_count, hold_cycles, tr.rst_n, vif.start, tr.tx_data),
					UVM_MEDIUM)
				end
				begin
					do begin
						@(vif.drv_cb);
					end while (vif.busy == 1);

					`uvm_info(get_type_name(),
					$sformatf("For %0d/%0d transaction to DUT: receiving busy = 0, proceed to next sequence",
						tr.seq_index, tr.seq_count),
					UVM_MEDIUM)
				end
			join

		end
	endtask
endclass
