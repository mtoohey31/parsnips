<script lang="ts">
  import init, { Emulator } from "parsnips-emu";
  import { onMount } from "svelte";

  onMount(async () => {
    await init();

    let prog = new Uint8Array(new Uint32Array([
      0b001001_00000_00011_1000001101101001,
      0b001001_00000_00010_1011000100111011,
      0b000000_00010_00011_00100_00101_100100,
    ]).buffer);

    let emu = new Emulator();

    emu.step(prog);
    emu.step(prog);
    emu.step(prog);
    console.log(emu.get_reg(4) == 0b1000000100101001);

    emu.free();

    prog = new Uint8Array(new Uint32Array([0b000000_00010_00011_00100_00101_111111]).buffer);

    emu = new Emulator();

    try {
      emu.step(prog);
    } catch (e) {
      console.log(e == "invalid function 0b111111");
    }
  });
</script>
