(() => {
  function getCodeText(code) {
    const lines = code.querySelectorAll(".giallo-l");
    if (lines.length === 0) return code.innerText.replace(/\n$/, "");

    return Array.from(lines, (line) => {
      const copy = line.cloneNode(true);
      copy.querySelectorAll(".giallo-ln").forEach((number) => number.remove());
      return copy.innerText;
    }).join("\n");
  }

  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      await navigator.clipboard.writeText(text);
      return;
    }

    const textarea = document.createElement("textarea");
    textarea.value = text;
    textarea.setAttribute("readonly", "");
    textarea.style.position = "fixed";
    textarea.style.opacity = "0";
    document.body.append(textarea);
    textarea.select();
    const copied = document.execCommand("copy");
    textarea.remove();
    if (!copied) throw new Error("Clipboard copy failed");
  }

  document.querySelectorAll("pre > code").forEach((code) => {
    const pre = code.parentElement;
    const button = document.createElement("button");
    button.type = "button";
    button.className = "copy-code-button";
    button.textContent = "Copy";
    button.setAttribute("aria-label", "Copy code to clipboard");

    button.addEventListener("click", async () => {
      try {
        await copyText(getCodeText(code));
        button.textContent = "Copied";
        button.dataset.copyState = "copied";
      } catch {
        button.textContent = "Copy failed";
        button.dataset.copyState = "error";
      }

      window.setTimeout(() => {
        button.textContent = "Copy";
        delete button.dataset.copyState;
      }, 1800);
    });

    pre.append(button);
  });
})();
