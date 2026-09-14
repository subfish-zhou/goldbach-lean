/* Load the existing dependency inspector only when a reader requests it. */
"use strict";
for (const panel of document.querySelectorAll("details.dependency-panel")) {
  panel.addEventListener("toggle", () => {
    if (!panel.open || panel.querySelector("iframe")) return;
    const target = new URL(panel.dataset.dependencySrc, location.href);
    if (target.origin !== location.origin || !target.pathname.endsWith("/structure/index.html")) {
      panel.querySelector(".dependency-host").textContent = "Invalid dependency route.";
      return;
    }
    const frame = document.createElement("iframe");
    frame.className = "dependency-frame";
    frame.title = "Compiled dependencies of " + target.searchParams.get("decl");
    frame.src = target.href;
    panel.querySelector(".dependency-host").append(frame);
  });
}
